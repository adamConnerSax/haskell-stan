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

-- This weirdness avoids overlapping instances issues
runGroupBuilder :: forall es x a . (EffF.Fail :> es, EffS.State SBC.StanCode :> es)
                   => x -> Eff (EffS.State (SBC.RowInfoMakers x) ': EffS.State (SBC.RowInfos x) ': es) a -> Eff (EffS.State (SBC.RowInfos x) ': es) a
runGroupBuilder x m = do
  (a, rowInfoMakers) <- EffS.runState DHash.empty m
  let rowInfos = DHash.mapWithKey (buildRowInfo x) rowInfoMakers
  EffS.put rowInfos
  addDataLengths @x
  buildGroupIndexes @x
  pure a

runStanBuilderEff :: forall md gq a . md -> gq -> SBC.StanBuilderEff md gq a -> Either Text (SBC.BuilderState md gq, [Text], a)
runStanBuilderEff md gq m = do
  let effRes =  Eff.runPureEff
                . EffF.runFail
                . EffW.runWriter
                . EffS.runState mempty
                . EffS.runState mempty
                . EffS.runState Set.empty
                . EffS.runState (SBC.StanCode SLP.SBData SLP.emptyStanProgram)
                . EffS.runState (SBPT.BParameterCollection mempty mempty)
                . EffS.runState DHash.empty
                . runGroupBuilder gq
                . EffS.runState DHash.empty
                . runGroupBuilder md
                $ m
  case effRes of
    Left err -> Left $ toText err
    Right ((((((((a, mRBs), gqRBs), pc), c), hf), mCJFs), gqCJFs), logs) -> do
      pure (SBC.BuilderState mRBs gqRBs mCJFs gqCJFs hf pc c, Foldl.fold Foldl.list logs, a)

-- build a new RowInfo from the row index and IntMap builders
buildRowInfo :: d -> SBC.RowTypeTag r -> SBC.GroupIndexAndIntMapMakers d r -> SBC.RowInfo d r
buildRowInfo d _rtt (SBC.GroupIndexAndIntMapMakers tf@(SBC.ToFoldable f) ims imbs) = Foldl.fold fld $ f d  where
  gisFld = indexBuildersForDataSetFold ims
--  uBindings = Map.insert (dataSetName rtt) (SLE.namedLIndex ("N_" <> dataSetName rtt))
--                $ useBindingsFromGroupIndexMakers rtt ims
  fld = SBC.RowInfo tf {- uBindings -} <$> gisFld <*> pure imbs <*> pure mempty

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

addDataLengths :: forall x es . (EffF.Fail :> es, EffS.State SBC.StanCode :> es
                                , EffS.State (SBC.RowInfos x) :> es) => Eff es ()
addDataLengths = do
  let addDataLength :: SBC.RowTypeTag r -> SBC.RowInfo x r -> Eff es (Maybe r)
      addDataLength rtt ri = case ri of
        SBC.RowInfo {} -> SBJ.addLengthJson rtt ("N_" <> SBC.dataSetName rtt) >> pure Nothing
  _ <- EffS.get @(SBC.RowInfos x) >>= DHash.traverseWithKey addDataLength
  pure ()

buildGroupIndexes :: forall x es . (EffF.Fail :> es, EffS.State SBC.StanCode :> es
                                   , EffS.State (SBC.RowInfos x) :> es)
                  => Eff es ()
buildGroupIndexes = do
  let buildIndexJSONFold :: (EffS.State (SBC.RowInfos (SBC.DataSource r)) :> es)
                         => SBC.RowTypeTag r -> SBC.GroupTypeTag k -> SBC.IndexMap r k -> Eff es (Maybe k)
      buildIndexJSONFold rtt gtt@(SBC.GroupTypeTag _gName lE) (SBC.IndexMap (SBC.IntIndex _gSize mIntF) _ _ _) = do
        let indexName = SBC.groupIndexVarName rtt gtt --dsName <> "_" <> gName
            ndsF x = SLS.NamedDeclSpec indexName $  SLS.addVMs (SLS.Modifiers [SLS.lowerM $ SLE.intE 1]) $ SLS.intArraySpec x
            mIntF' x = case mIntF x of
              Left msg -> Left $ msg <> " (from buildGroupIndexes for indexName=" <> indexName <> ")"
              Right y -> Right y
        _ <- SBJ.addColumnMJson rtt ndsF lE mIntF'
        pure Nothing
      buildRowFolds :: EffS.State (SBC.RowInfos d) :> es => SBC.RowTypeTag r -> SBC.RowInfo d r -> Eff es (Maybe r)
      buildRowFolds rtt ri  = case ri of
        SBC.RowInfo _ (SBC.GroupIndexes gis) _ _ -> do
          _ <- DHash.traverseWithKey (buildIndexJSONFold rtt) gis
          pure Nothing
  _ <- EffS.get @(SBC.RowInfos x) >>= DHash.traverseWithKey buildRowFolds
  pure ()
