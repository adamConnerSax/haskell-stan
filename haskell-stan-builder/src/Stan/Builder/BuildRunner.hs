{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Stan.Builder.BuildRunner
  (
    module Stan.Builder.BuildRunner
  )
where

import qualified Stan.Builder.Core as SBC
import qualified Stan.Builder.Data as SBD
import qualified Stan.Builder.Groups as SBG
import qualified Stan.Builder.JSON as SBJ

import qualified Stan.Language.Program as SLP
import qualified Stan.Language.Expressions as SLE
import qualified Stan.Language.Statement as SLS
import qualified Stan.Language.Statements as SLS
import qualified Stan.Builder.Parameters.Types as SBPT

import Prelude hiding (All)
import qualified Control.Foldl as Foldl
import qualified Data.Dependent.HashMap as DHash
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import qualified Effectful as Eff
import Effectful ((:>), Eff)
import qualified Effectful.State.Static.Local as EffS
import qualified Effectful.Writer.Static.Local as EffW
import qualified Effectful.Fail as EffF

{-
-- This weirdness avoids overlapping instances issues
runGroupBuilder' :: forall es i a . (SBC.StanCodeC es, EffS.State SBC.JSONNames :> es)
                => SBC.DataSource i
                -> Eff (EffS.State (SBC.RowInfoMakers i) ': EffS.State (SBC.RowInfos i) ': es) a
                -> Eff (EffS.State (SBC.RowInfos i) ': es) a
runGroupBuilder' x m = do
  (a, rowInfoMakers) <- EffS.runState DHash.empty m
  let rowInfos = DHash.mapWithKey (buildRowInfo x) rowInfoMakers
  EffS.put rowInfos
  addDataLengths @i
  buildGroupIndexes @i
  pure a
-}

setupDataAndGroups :: forall es i a . (SBC.StanConstJsonC i es, SBC.StanRowInfoC i es)
                   => SBC.DataSource i
                   -> SBC.StanDataBuilderEff i a
                   -> Eff es a
setupDataAndGroups d sgb = do
  let gbRes = Eff.runPureEff
              . EffF.runFail
              . EffW.runWriter
              . EffS.runState (SBC.JSONNames Set.empty)
              . EffS.runState mempty
              . EffS.runState (SBC.StanCode SLP.SBData SLP.emptyStanProgram)
              . EffS.runState DHash.empty
              $ sgb
  case gbRes of
    Left err -> SBC.buildError $ toText err -- propagate the error state
    Right (((((a, rowInfoMakers), code), jcf), jsonNames), logs) -> do
      EffW.tell logs -- add the builder logs
      mergeCode code
      checkAndMergeJSONNames jsonNames
      EffS.put jcf -- add the const folds from groups (group sizes)
      let rowInfos = DHash.mapWithKey (buildRowInfo d) rowInfoMakers
      EffS.put rowInfos
      addDataLengths @i
      buildGroupIndexes @i
      pure a

checkAndMergeJSONNames :: (EffF.Fail :> es, EffS.State SBC.JSONNames :> es) => SBC.JSONNames -> Eff es ()
checkAndMergeJSONNames (SBC.JSONNames newNames) = do
  existingNames <- EffS.gets SBC.unJSONNames
  let overlap = Set.intersection newNames existingNames
  if (Set.size overlap == 0)
    then EffS.modify $ SBC.JSONNames . Set.union newNames . SBC.unJSONNames
    else SBC.buildError $ "overlapping names when setting up data & groups: " <> show overlap

mergeCode :: EffS.State SBC.StanCode :> es => SBC.StanCode -> Eff es ()
mergeCode (SBC.StanCode cb sp) = do
  let f (SBC.StanCode _ sp') = SBC.StanCode cb (sp' <> sp)
  EffS.modify f

runStanBuilderEff :: forall a b c .
                     SBC.DataSource SBC.ModelDataT
                  -> SBC.DataSource SBC.GQDataT
                  -> SBC.StanDataBuilderEff SBC.ModelDataT a
                  -> (a -> SBC.StanDataBuilderEff SBC.GQDataT b)
                  -> (a -> b -> SBC.StanModelBuilderEff c)
                  -> Either Text (SBC.BuilderState, [Text], c)
runStanBuilderEff md gq modelDG gqDG stanBuilderF = do
  let m' = setupDataAndGroups md modelDG >>= \a -> setupDataAndGroups gq (gqDG a) >>= \b -> stanBuilderF a b
  let effRes =  Eff.runPureEff
                . EffF.runFail
                . EffW.runWriter
                . EffS.runState (SBC.JSONNames Set.empty)
                . EffS.runState mempty
                . EffS.runState mempty
                . EffS.runState (SBC.FunctionNames Set.empty)
                . EffS.runState (SBC.StanCode SLP.SBData SLP.emptyStanProgram)
                . EffS.runState (SBPT.BParameterCollection mempty mempty)
                . EffS.runState DHash.empty
--                . runGroupBuilder gq
                . EffS.runState DHash.empty
--                . runGroupBuilder md
                $ m'
  case effRes of
    Left err -> Left $ toText err
    Right (((((((((a, mRBs), gqRBs), pc), c), hf), mCJFs), gqCJFs), _hj), logs) -> do
      pure (SBC.BuilderState mRBs gqRBs mCJFs gqCJFs (SBC.unFunctionNames hf) pc c, Foldl.fold Foldl.list logs, a)

-- build a new RowInfo from the row index and IntMap builders
buildRowInfo :: d -> SBC.RowTypeTag i r -> SBC.GroupIndexAndIntMapMakers d r -> SBC.RowInfo d r
buildRowInfo d _rtt (SBC.GroupIndexAndIntMapMakers tf@(SBC.ToFoldable f) ims imbs) = Foldl.fold fld $ f d  where
  gisFld = indexBuildersForDataSetFold ims
  fld = SBC.RowInfo tf <$> gisFld <*> pure imbs <*> pure mempty

indexBuildersForDataSetFold :: SBC.GroupIndexMakers r -> Foldl.Fold r (SBC.GroupIndexes r)
indexBuildersForDataSetFold (SBC.GroupIndexMakers gims) = SBC.GroupIndexes <$> DHash.traverse makeIndexMapF gims

makeIndexMapF :: SBC.MakeIndex r k -> Foldl.Fold r (SBC.IndexMap r k)
makeIndexMapF (SBC.GivenIndex m h) = pure $ mapToIndexMap h m
makeIndexMapF (SBC.FoldToIndex fld h) = fmap (mapToIndexMap h) fld


mapLookupE :: Ord k => (k -> Text) -> Map k a -> k -> Either Text a
mapLookupE errMsg m k = case Map.lookup k m of
  Just a -> Right a
  Nothing -> Left $ errMsg k

toIntMap :: Map k Int -> IntMap k
toIntMap = IntMap.fromList . fmap (\(a, b) -> (b, a)) . Map.toList

mapToIndexMap :: Ord k => (r -> k) -> Map k Int -> SBC.IndexMap r k
mapToIndexMap h m = indxMap where
  lookupK = mapLookupE (const $ "key not found when building given index") m
  intIndex = SBC.IntIndex (Map.size m) (lookupK . h)
  indxMap = SBC.IndexMap intIndex lookupK (toIntMap m) h

addDataLengths :: forall i es . SBC.StanJsonC i es => Eff es ()
addDataLengths = do
  let addDataLength :: SBC.RowTypeTag i r -> SBC.RowInfo (SBC.DataSource i) r -> Eff es (Maybe r)
      addDataLength rtt ri = case ri of
        SBC.RowInfo {} -> SBJ.addLengthJson SBJ.ErrIfDuplicate rtt ("N_" <> SBC.dataSetName rtt) >> pure Nothing
  _ <- EffS.get @(SBC.RowInfos i) >>= DHash.traverseWithKey addDataLength
  pure ()

buildGroupIndexes :: forall i es . SBC.StanJsonC i es
                  => Eff es ()
buildGroupIndexes = do
  let buildIndexJSONFold :: SBC.RowTypeTag i r -> SBC.GroupTypeTag k -> SBC.IndexMap r k -> Eff es (Maybe k)
      buildIndexJSONFold rtt gtt@(SBC.GroupTypeTag _gName) (SBC.IndexMap (SBC.IntIndex _gSize mIntF) _ _ _) = do
        let indexName = SBG.groupIndexVarName rtt gtt --dsName <> "_" <> gName
            ndsF x = SLS.NamedDeclSpec indexName
                     $ SLS.addVMs (SLS.Modifiers [SLS.lowerM $ SLE.intE 1, SLS.upperM $ SBC.groupSizeE gtt])
                     $ SLS.intArraySpec x
            mIntF' x = case mIntF x of
              Left msg -> Left $ msg <> " (from buildGroupIndexes for indexName=" <> indexName <> ")"
              Right y -> Right y
        _ <- SBJ.addColumnMJson SBJ.ErrIfDuplicate rtt ndsF (SBD.dataSetSizeE rtt) mIntF'
        pure Nothing
      buildRowFolds :: SBC.RowTypeTag i r -> SBC.RowInfo d r -> Eff es (Maybe r)
      buildRowFolds rtt ri  = case ri of
        SBC.RowInfo _ (SBC.GroupIndexes gis) _ _ -> do
          _ <- DHash.traverseWithKey (buildIndexJSONFold rtt) gis
          pure Nothing
  _ <- EffS.get @(SBC.RowInfos i) >>= DHash.traverseWithKey buildRowFolds
  pure ()
