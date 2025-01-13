{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Stan.Builder.JSON
  (
    module Stan.Builder.JSON
  )
where

import qualified Stan.Builder.JSON.JSONUtils as SBJU
import qualified Stan.Builder.Core as SBC
import qualified Stan.Builder.Build as SBB

import qualified Stan.Language.Types as SLT
import qualified Stan.Language.Program as SLP
import qualified Stan.Language.Expression as SLE
import qualified Stan.Language.Expressions as SLE
import qualified Stan.Language.Statement as SLS
import qualified Stan.Language.Statements as SLS
import qualified Stan.Language.CodeWriter as SLC

import Prelude hiding (All)
import qualified Control.Foldl as Foldl
import qualified Data.Aeson as Aeson
import qualified Data.Dependent.HashMap as DHash
import qualified Data.Text as T
import qualified Data.Dependent.Sum as DSum
import qualified Data.Vector.Unboxed as VU

import Effectful ((:>), Eff)
import qualified Effectful.State.Static.Local as EffS
import qualified Effectful.Fail as EffF

type AddJsonC r es = (EffF.Fail :> es, EffS.State SBC.StanCode :> es, EffS.State (SBC.RowInfos (SBC.DataSource r)) :> es)
type AddConstJsonC i es = (EffF.Fail :> es, EffS.State (SBC.JSONConstFold (SBC.SourceType i)) :> es, EffS.State SBC.StanCode :> es)

data MatrixRowFromData r = MatrixRowFromData { rowName :: SLT.VarName, colIndexM :: Maybe SLT.VarName, rowLength :: Int, rowVec :: r -> VU.Vector Double }

add2dMatrixJson :: AddJsonC r es
                => SBC.RowTypeTag r
                -> MatrixRowFromData r
                -> SLS.VarModifiers SLE.UExpr SLT.EReal
                -> SLE.IntE
                -> SLE.IntE
                -> Eff es SLE.MatrixE
add2dMatrixJson rtt (MatrixRowFromData vName _ _ vecF) cs rowsE colsE = do
  let dsName = SBC.dataSetName rtt
      wdName = tName <> underscoredIf dsName
      ndsF rowsE' = SLS.NamedDeclSpec wdName $ SLS.addVMs cs $ SLS.matrixSpec rowsE' colsE
--      idt = SBC.dataSetInputDataT rtt
  addColumnJson rtt ndsF rowsE vecF

mrfdColumnsName :: MatrixRowFromData r -> SLT.VarName
mrfdColumnsName mrfd = "K_" <> fromMaybe mrfd.rowName mrfd.colIndexM

addColumnMJson :: (Aeson.ToJSON x, AddJsonC r es)
               => SBC.RowTypeTag r
               -> (SLE.IntE -> SLS.NamedDeclSpec t)
               -> SLE.IntE
               -> (r -> Either Text x)
               -> Eff es (SLE.UExpr t)
addColumnMJson rtt ndsF lengthE toMX = do
  let nds = ndsF lengthE
  addJson rtt nds (SBJU.valueToPairF (SLS.declName nds) $ SBJU.jsonArrayEF toMX)

addColumnJson :: (Aeson.ToJSON x, AddJsonC r es)
              => SBC.RowTypeTag r
              -> (SLE.IntE -> SLS.NamedDeclSpec t)
              -> SLE.IntE
              -> (r -> x)
              -> Eff es (SLE.UExpr t)
addColumnJson rtt ndsF lengthE toX = do
  let nds = ndsF lengthE
  addJson rtt nds (SBJU.valueToPairF (SLS.declName nds) $ SBJU.jsonArrayF toX)


addLengthJson :: AddJsonC r es
              => SBC.RowTypeTag r
              -> SLT.VarName
              -> Eff es SLE.IntE
addLengthJson rtt tName = addJson rtt (SLS.NamedDeclSpec tName ds) (SBJU.namedF tName Foldl.length)
  where
    ds = SLS.addVMs (SLS.Modifiers [SLS.lowerM $ SLE.intE 1]) SLS.intSpec


buildJSONF :: forall x es . EffS.State (SBC.RowInfos x) :> es => Eff es (DHash.DHashMap SBC.RowTypeTag (JSONRowFold x))
buildJSONF = do
  rowInfos <- EffS.get --modelRowBuilders <$> get
  let bldRowJSONFolds :: SBC.RowInfo x r -> Eff es (JSONRowFold x r)
      bldRowJSONFolds (SBC.RowInfo tf _ _ (SBC.JSONSeriesFold jsonF)) = pure $ JSONRowFold tf jsonF
  DHash.traverse bldRowJSONFolds rowInfos
{-
buildGQJSONF :: forall md gq . StanBuilderM md gq (DHash.DHashMap RowTypeTag (JSONRowFold gq))
buildGQJSONF = do
  rowInfos <- gqRowBuilders <$> get
  DHash.traverse buildRowJSONFolds rowInfos

buildRowJSONFolds :: RowInfo d r -> Eff es (JSONRowFold d r)
buildRowJSONFolds ri = pure $ JSONRowFold (toFoldable ri) jsonF where
  JSONSeriesFold jsonF = jsonSeries ri
-}

buildJSONFromDataM :: forall x es . (EffS.State (SBC.RowInfos x) :> es, EffS.State (SBC.JSONConstFold x) :> es)
                   => Eff es (x -> Either Text Aeson.Series)
buildJSONFromDataM = do
  (SBC.JSONConstFold constJSONFld) <- EffS.get @(SBC.JSONConstFold x)
  dataSetJSON <- buildJSONF
  pure $ \d ->
    let c = Foldl.foldM constJSONFld (Just ())
        ds =  buildJSONFromRows dataSetJSON d
    in (<>) <$> c <*> ds

{-
buildGQJSONFromDataM :: StanBuilderM md gq (gq -> Either Text Aeson.Series)
buildGQJSONFromDataM = do
  (JSONSeriesFold constJSONFld) <- constGQJSON <$> get
  dataSetJSON <- buildGQJSONF
  return $ \d ->
    let c = Foldl.foldM constJSONFld (Just ())
        ds =  buildJSONFromRows dataSetJSON d
    in (<>) <$> c <*> ds
-}

buildJSONSeries :: forall d. SBC.RowInfos d -> d -> Either Text Aeson.Series
buildJSONSeries rbm d =
  let foldOne :: SBC.RowBuilder d -> Either Text Aeson.Series
      foldOne ((SBC.RowTypeTag _ _) DSum.:=> (SBC.RowInfo (SBC.ToFoldable f)  _ _ (SBC.JSONSeriesFold fld))) = Foldl.foldM fld (f d)
  in mconcat <$> (traverse foldOne $ DHash.toList rbm)

data JSONRowFold d r = JSONRowFold (SBC.ToFoldable d r) (SBJU.StanJSONF r Aeson.Series)

buildJSONFromRows :: DHash.DHashMap SBC.RowTypeTag (JSONRowFold d) -> d -> Either Text Aeson.Series
buildJSONFromRows rowFoldMap d = do
  let toSeriesOne (_ DSum.:=> JSONRowFold (SBC.ToFoldable tf) fld) = Foldl.foldM fld (tf d)
      res = fmap mconcat $ traverse toSeriesOne $ DHash.toList rowFoldMap
  res
  {-
  case res of
    Left err -> Left err
    Right s -> Left $ "buildJSONFromRows: pairs(series)=" <> show (Aeson.pairs s)
-}

modelJsonE :: SBC.BuilderState md gq -> md -> Either Text Aeson.Series
modelJsonE (SBC.BuilderState mRBs _ (SBC.JSONConstFold mCJF) _ _ _ _) md = (<>) <$> Foldl.foldM mCJF (Just ()) <*> buildJSONSeries mRBs md

gqJsonE :: SBC.BuilderState md gq -> gq -> Either Text Aeson.Series
gqJsonE (SBC.BuilderState _ gqRBs _ (SBC.JSONConstFold gqCJF) _ _ _) gq = (<>) <$> Foldl.foldM gqCJF (Just ()) <*> buildJSONSeries gqRBs gq

-- The Maybe return values are there just to satisfy the (returned) type of DHash.traverseWithKey
{-
buildGroupIndexes' :: forall md gq es . (EffF.Fail :> es, EffS.State SBC.StanCode :> es
                                       , EffS.State (SBC.RowInfos md) :> es, EffS.State (SBC.RowInfos gq) :> es) => Eff es ()
buildGroupIndexes' = do
  let buildIndexJSONFold :: (EffS.State (SBC.RowInfos (SBC.DataSource r)) :> es)
                         => SBC.RowTypeTag r -> SBC.GroupTypeTag k -> SBC.IndexMap r k -> Eff es (Maybe k)
      buildIndexJSONFold rtt gtt@(SBC.GroupTypeTag gName lE) (SBC.IndexMap (SBC.IntIndex gSize mIntF) _ _ _) = do
        let indexName = SBC.groupIndexVarName rtt gtt --dsName <> "_" <> gName
            ndsF x = SLS.NamedDeclSpec indexName $  SLS.addVMs (SLS.Modifiers [SLS.lowerM $ SLE.intE 1]) $ SLS.intArraySpec x
            mIntF' x = case mIntF x of
              Left msg -> Left $ msg <> " (from buildGroupIndexes for indexName=" <> indexName <> ")"
              Right y -> Right y
        _ <- addColumnMJson rtt ndsF lE mIntF'
        pure Nothing
      buildRowFolds :: EffS.State (SBC.RowInfos d) :> es => SBC.RowTypeTag r -> SBC.RowInfo d r -> Eff es (Maybe r)
      buildRowFolds rtt ri  = case ri of
        SBC.RowInfo _ (SBC.GroupIndexes gis) _ _ -> do
          _ <- DHash.traverseWithKey (buildIndexJSONFold rtt) gis
          pure Nothing
  _ <- EffS.get @(SBC.RowInfos md) >>= DHash.traverseWithKey buildRowFolds
  _ <- EffS.get @(SBC.RowInfos gq) >>= DHash.traverseWithKey buildRowFolds
  pure ()
-}




addFixedIntJson :: AddConstJsonC i es --(EffF.Fail :> es, EffS.State (SBC.JSONConstFold (SBC.SourceType i)) :> es, EffS.State SBC.StanCode :> es)
                => SBC.InputDataType i -> Text -> Maybe Int -> Int -> Eff es SLE.IntE
addFixedIntJson idt tName mLower n = do
  let ds = flip SLS.addVMs SLS.intSpec $ maybe SLS.NoModifiers (SLS.Modifiers . pure . SLS.lowerM . SLE.intE) mLower
      codeBlock = if SBC.inputDataT idt == SBC.ModelDataT then SLP.SBData else SLP.SBDataGQ
  ie <- SBB.inBlock codeBlock $ SBB.addFromCodeWriter $ SLC.declareW tName ds
  addConstJson idt (SBC.JSONConstFold $ SBJU.constDataF tName n)
  return ie -- $ TE.namedE tName TE.SInt

addConstJson :: forall i es . (EffS.State (SBC.JSONConstFold (SBC.SourceType i)) :> es)
             => SBC.InputDataType i -> SBC.JSONConstFold (SBC.SourceType i) -> Eff es ()
addConstJson _ (SBC.JSONConstFold jf) = do
  (SBC.JSONConstFold f) <- EffS.get @(SBC.JSONConstFold (SBC.SourceType i))
  EffS.put @(SBC.JSONConstFold (SBC.SourceType i)) $ SBC.JSONConstFold (f <> jf)

addJson :: forall t r es . AddJsonC r es
        => SBC.RowTypeTag r
        -> SLS.NamedDeclSpec t
        -> SBJU.StanJSONF r Aeson.Series
        -> Eff es (SLE.UExpr t)
addJson rtt nds fld = do
  let codeBlock = if SBC.dataSetInputDataT rtt == SBC.ModelDataT then SLP.SBData else SLP.SBDataGQ
  ve <- SBB.inBlock codeBlock $ SBB.addFromCodeWriter $ SLC.declareNW nds
  let addFold :: SBC.RowInfos (SBC.DataSource r) -> Eff es (SBC.RowInfos (SBC.DataSource r))
      addFold rowInfos = case addFoldToDBuilder rtt fld rowInfos of
        Nothing -> SBC.buildError $ "Attempt to add Json to an uninitialized dataset (" <> SBC.dataSetName rtt <> ")"
        Just x -> pure x
  oldRowInfos <- EffS.get @(SBC.RowInfos (SBC.DataSource r))
  newRowInfos <- addFold oldRowInfos
  EffS.put newRowInfos
  return ve

addFoldToDBuilder :: forall r.
                     SBC.RowTypeTag r
                  -> SBJU.StanJSONF r Aeson.Series
                  -> SBC.RowInfos (SBC.DataSource r)
                  -> Maybe (SBC.RowInfos (SBC.DataSource r))
addFoldToDBuilder rtt fld ris =
  case DHash.lookup rtt ris of
    Nothing -> Nothing --DHash.insert rtt (RowInfo (JSONSeriesFold fld) (const Nothing)) rbm
    Just (SBC.RowInfo x y z (SBC.JSONSeriesFold fld'))
      -> Just $ DHash.insert rtt (SBC.RowInfo x y z (SBC.JSONSeriesFold $ fld' <> fld)) ris

underscoredIf :: Text -> Text
underscoredIf t = if T.null t then "" else "_" <> t
