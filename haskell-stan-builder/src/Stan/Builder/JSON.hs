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
import qualified Data.Set as Set
import qualified Data.Text as T
import qualified Data.Dependent.Sum as DSum
import qualified Data.Vector.Unboxed as VU

import Effectful ((:>), Eff)
import qualified Effectful.State.Static.Local as EffS
import qualified Effectful.Fail as EffF

type AddJsonC i r es = (EffF.Fail :> es, EffS.State SBC.JSONNames :> es, EffS.State (SBC.RowInfos i (SBC.DataSource i)) :> es, EffS.State SBC.StanCode :> es)
type AddConstJsonC i es = (EffF.Fail :> es, EffS.State SBC.JSONNames :> es, EffS.State (SBC.JSONConstFold (SBC.DataSource i)) :> es, EffS.State SBC.StanCode :> es)

data MatrixRowFromData r = MatrixRowFromData { rowName :: SLT.VarName, colIndexM :: Maybe SLT.VarName, rowLength :: Int, rowVec :: r -> VU.Vector Double }

data JSONAddStyle = ErrIfDuplicate | IgnoreIfDuplicate deriving stock (Show, Eq)

add2dMatrixJson :: AddJsonC i r es
                => JSONAddStyle
                -> SBC.RowTypeTag i r
                -> MatrixRowFromData r
                -> SLS.VarModifiers SLE.UExpr SLT.EReal
                -> SLE.IntE
                -> SLE.IntE
                -> Eff es SLE.MatrixE
add2dMatrixJson jas rtt (MatrixRowFromData vName _ _ vecF) cs rowsE colsE = do
  let dsName = SBC.dataSetName rtt
      wdName = vName <> underscoredIf dsName
      ndsF rowsE' = SLS.NamedDeclSpec wdName $ SLS.addVMs cs $ SLS.matrixSpec rowsE' colsE
--      idt = SBC.dataSetInputDataT rtt
  addColumnJson jas rtt ndsF rowsE vecF

mrfdColumnsName :: MatrixRowFromData r -> SLT.VarName
mrfdColumnsName mrfd = "K_" <> fromMaybe mrfd.rowName mrfd.colIndexM

addColumnMJson :: (Aeson.ToJSON x, AddJsonC i r es)
               => JSONAddStyle
               -> SBC.RowTypeTag i r
               -> (SLE.IntE -> SLS.NamedDeclSpec t)
               -> SLE.IntE
               -> (r -> Either Text x)
               -> Eff es (SLE.UExpr t)
addColumnMJson jas rtt ndsF lengthE toMX = do
  let nds = ndsF lengthE
  addJson jas rtt nds (SBJU.valueToPairF (SLS.declName nds) $ SBJU.jsonArrayEF toMX)

addColumnJson :: (Aeson.ToJSON x, AddJsonC i r es)
              => JSONAddStyle
              -> SBC.RowTypeTag i r
              -> (SLE.IntE -> SLS.NamedDeclSpec t)
              -> SLE.IntE
              -> (r -> x)
              -> Eff es (SLE.UExpr t)
addColumnJson jas rtt ndsF lengthE toX = do
  let nds = ndsF lengthE
  addJson jas rtt nds (SBJU.valueToPairF (SLS.declName nds) $ SBJU.jsonArrayF toX)


addLengthJson :: AddJsonC i r es
              => JSONAddStyle
              -> SBC.RowTypeTag i r
              -> SLT.VarName
              -> Eff es SLE.IntE
addLengthJson jas rtt tName = addJson jas rtt (SLS.NamedDeclSpec tName ds) (SBJU.namedF tName Foldl.length)
  where
    ds = SLS.addVMs (SLS.Modifiers [SLS.lowerM $ SLE.intE 1]) SLS.intSpec


addFixedIntJson :: AddConstJsonC i es --(EffF.Fail :> es, EffS.State (SBC.JSONConstFold (SBC.SourceType i)) :> es, EffS.State SBC.StanCode :> es)
                => JSONAddStyle -> SBC.InputDataType i -> Text -> Maybe Int -> Int -> Eff es SLE.IntE
addFixedIntJson jas idt vName mLower n = do
  let ds = flip SLS.addVMs SLS.intSpec $ maybe SLS.NoModifiers (SLS.Modifiers . pure . SLS.lowerM . SLE.intE) mLower
--      codeBlock = if SBC.inputDataT idt == SBC.ModelDataT then SLP.SBData else SLP.SBDataGQ
--  ie <- SBB.inBlock codeBlock $ SBB.addFromCodeWriter $ SLC.declareW tName ds
  addConstJson jas (SLS.NamedDeclSpec vName ds) idt (SBC.JSONConstFold $ SBJU.constDataF vName n)


addConstJson :: forall i t es . AddConstJsonC i es
             => JSONAddStyle
             -> SLS.NamedDeclSpec t
             -> SBC.InputDataType i
             -> SBC.JSONConstFold (SBC.DataSource i)
             -> Eff es (SLE.UExpr t)
addConstJson jas nds idt (SBC.JSONConstFold jf) = do
  let jsonName = SLS.declName nds
  jn <- EffS.gets SBC.unJSONNames
  case jsonName `Set.member` jn of
    True -> if jas == IgnoreIfDuplicate
            then pure $ SLE.namedE jsonName $ SLS.declSType $ SLS.decl nds
            else SBC.buildError $ "addConstJSON: " <> jsonName <> " already added and JSONAddStyle is ErrIfDuplicate"
    False -> do
      (SBC.JSONConstFold f) <- EffS.get @(SBC.JSONConstFold (SBC.DataSource i))
      EffS.put @(SBC.JSONConstFold (SBC.DataSource i)) $ SBC.JSONConstFold (f <> jf)
      EffS.modify (SBC.JSONNames . Set.insert jsonName . SBC.unJSONNames)
      SBB.inBlock (codeBlock idt) $ SBB.addFromCodeWriter $ SLC.declareNW nds

codeBlock :: SBC.InputDataType i -> SLP.StanBlock
codeBlock = \case
  SBC.ModelData -> SLP.SBData
  SBC.GQData -> SLP.SBDataGQ

addJson :: forall t i r es . AddJsonC i r es
        => JSONAddStyle
        -> SBC.RowTypeTag i r
        -> SLS.NamedDeclSpec t
        -> SBJU.StanJSONF r Aeson.Series
        -> Eff es (SLE.UExpr t)
addJson jas rtt nds fld = do
  let jsonName = SLS.declName nds
  jn <- EffS.gets SBC.unJSONNames
  case jsonName `Set.member` jn of
    True -> if jas == IgnoreIfDuplicate
      then pure $ SLE.namedE jsonName $ SLS.declSType $ SLS.decl nds
      else SBC.buildError $ "addJSON: " <> jsonName <> " already added and JSONAddStyle is ErrIfDuplicate"
    False -> do
--      let codeBlock = if SBC.dataSetInputDataT rtt == SBC.ModelData then SLP.SBData else SLP.SBDataGQ
      ve <- SBB.inBlock (codeBlock $ SBC.dataSetInputData rtt) $ SBB.addFromCodeWriter $ SLC.declareNW nds
      let addFold :: SBC.RowInfos i (SBC.DataSource i) -> Eff es (SBC.RowInfos i (SBC.DataSource i))
          addFold rowInfos = case addFoldToDBuilder rtt fld rowInfos of
            Nothing -> SBC.buildError $ "Attempt to add Json to an uninitialized dataset (" <> SBC.dataSetName rtt <> ")"
            Just x -> pure x
      oldRowInfos <- EffS.get @(SBC.RowInfos i (SBC.DataSource i))
      newRowInfos <- addFold oldRowInfos
      EffS.put newRowInfos
      pure ve

addFoldToDBuilder :: forall i r.
                     SBC.RowTypeTag i r
                  -> SBJU.StanJSONF r Aeson.Series
                  -> SBC.RowInfos i (SBC.DataSource i)
                  -> Maybe (SBC.RowInfos i (SBC.DataSource i))
addFoldToDBuilder rtt fld ris =
  case DHash.lookup rtt ris of
    Nothing -> Nothing --DHash.insert rtt (RowInfo (JSONSeriesFold fld) (const Nothing)) rbm
    Just (SBC.RowInfo x y z (SBC.JSONSeriesFold fld'))
      -> Just $ DHash.insert rtt (SBC.RowInfo x y z (SBC.JSONSeriesFold $ fld' <> fld)) ris

underscoredIf :: Text -> Text
underscoredIf t = if T.null t then "" else "_" <> t

buildJSONF :: forall i x es . EffS.State (SBC.RowInfos i x) :> es => Eff es (DHash.DHashMap (SBC.RowTypeTag i) (JSONRowFold x))
buildJSONF = do
  rowInfos <- EffS.get --modelRowBuilders <$> get
  let bldRowJSONFolds :: SBC.RowInfo x r -> Eff es (JSONRowFold x r)
      bldRowJSONFolds (SBC.RowInfo tf _ _ (SBC.JSONSeriesFold jsonF)) = pure $ JSONRowFold tf jsonF
  DHash.traverse bldRowJSONFolds rowInfos


buildJSONFromDataM :: forall i x es . (EffS.State (SBC.RowInfos i x) :> es, EffS.State (SBC.JSONConstFold x) :> es)
                   => Eff es (x -> Either Text Aeson.Series)
buildJSONFromDataM = do
  (SBC.JSONConstFold constJSONFld) <- EffS.get @(SBC.JSONConstFold x)
  dataSetJSON <- buildJSONF @i
  pure $ \d ->
    let c = Foldl.foldM constJSONFld (Just ())
        ds =  buildJSONFromRows dataSetJSON d
    in (<>) <$> c <*> ds

buildJSONSeries :: forall i d. SBC.RowInfos i d -> d -> Either Text Aeson.Series
buildJSONSeries rbm d =
  let foldOne :: SBC.RowBuilder i d -> Either Text Aeson.Series
      foldOne ((SBC.RowTypeTag _ _) DSum.:=> (SBC.RowInfo (SBC.ToFoldable f)  _ _ (SBC.JSONSeriesFold fld))) = Foldl.foldM fld (f d)
  in mconcat <$> (traverse foldOne $ DHash.toList rbm)

data JSONRowFold d r = JSONRowFold (SBC.ToFoldable d r) (SBJU.StanJSONF r Aeson.Series)

buildJSONFromRows :: DHash.DHashMap (SBC.RowTypeTag i) (JSONRowFold d) -> d -> Either Text Aeson.Series
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

{-
buildGQJSONF :: forall md gq . StanBuilderM md gq (DHash.DHashMap RowTypeTag (JSONRowFold gq))
buildGQJSONF = do
  rowInfos <- gqRowBuilders <$> get
  DHash.traverse buildRowJSONFolds rowInfos

buildRowJSONFolds :: RowInfo d r -> Eff es (JSONRowFold d r)
buildRowJSONFolds ri = pure $ JSONRowFold (toFoldable ri) jsonF where
  JSONSeriesFold jsonF = jsonSeries ri
-}
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
