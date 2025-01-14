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

module Stan.Builder.Groups
  (
    module Stan.Builder.Groups
  )
where

import qualified Stan.Builder.Core as SBC
import qualified Stan.Builder.JSON as SBJ

import Prelude hiding (All)
import qualified Control.Foldl as Foldl
import qualified Data.Dependent.HashMap as DHash
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import Effectful ((:>), Eff)
import qualified Effectful.State.Static.Local as EffS
import qualified Effectful.Fail as EffF

type AddGroup k es = (Typeable k, SBJ.AddConstJsonC SBC.ModelDataT es)

addGroup :: forall k es . AddGroup k es
         => Text -> Int -> Eff es (SBC.GroupTypeTag k)
addGroup groupName size = do
  lE <- SBJ.addFixedIntJson SBJ.ErrIfDuplicate SBC.ModelData ("J_" <> groupName) (Just 1) size
  pure $ SBC.GroupTypeTag groupName lE

addEnumGroup :: forall k es . (Enum k, Bounded k, AddGroup k es)
             => Text
             -> Eff es (SBC.GroupTypeTag k)
addEnumGroup groupName = addGroup groupName size
  where
    size = Foldl.fold Foldl.length $ ([minBound..maxBound] :: [k])

addGroupFromCollection :: forall k f es . (Ord k, Foldable f, AddGroup k es)
                       => Text -> f k -> Eff es (SBC.GroupTypeTag k)
addGroupFromCollection groupName c = addGroup groupName size
  where
    size = Set.size $ Foldl.fold Foldl.set c

makeIndexFromEnum :: forall k r . (Enum k, Bounded k, Ord k) => (r -> k) -> SBC.MakeIndex r k
makeIndexFromEnum h = SBC.GivenIndex m h where
  allKs = [minBound..maxBound]
  m = Map.fromList $ zip allKs [1..]

makeIndexFromFoldable :: (Foldable f, Ord k)
  => (k -> Text)
  -> (r -> k)
  -> f k
  -> SBC.MakeIndex r k
makeIndexFromFoldable _ h allKs = SBC.GivenIndex asMap h where
  listKs = ordNub $ Foldl.fold Foldl.list allKs
  asMap = Map.fromList $ zip listKs [1..]

makeIndexByCounting :: Ord k => (k -> Text) -> (r -> k) -> SBC.MakeIndex r k
makeIndexByCounting printK h = SBC.FoldToIndex (Foldl.premap h $ indexFold printK 1) h

indexFold :: Ord k => (k -> Text) -> Int -> Foldl.Fold k (Map k Int)
indexFold _ start =  Foldl.Fold step Set.empty done where
  step s k = Set.insert k s
  done s = mapToInt where
    keyedList = zip (Set.toList s) [start..]
    mapToInt = Map.fromList keyedList


addGroupIndexForData :: forall r k es . (EffF.Fail :> es, EffS.State (SBC.RowInfoMakers (SBC.DataSource r)) :> es)
                     => SBC.GroupTypeTag k
                     -> SBC.RowTypeTag r
                     -> SBC.MakeIndex r k
                     -> Eff es ()
addGroupIndexForData gtt rtt mkIndex = withRowInfoMakers @(SBC.DataSource r) f where
  idt = SBC.dataSetInputDataT rtt
  f :: forall x. SBC.RowInfoMakers x -> Eff es (Maybe (SBC.RowInfoMakers x), ())
  f rowInfoMakers = do
    case DHash.lookup rtt rowInfoMakers of
      Nothing -> SBC.buildError $ "Data-set \"" <> SBC.dataSetName rtt <> "\" needs to be added to " <> show idt <> " before groups can be added to it."
      Just (SBC.GroupIndexAndIntMapMakers tf (SBC.GroupIndexMakers gims) gimbs) -> case DHash.lookup gtt gims of
        Just _ -> SBC.buildError
                  $ "Attempt to add a second group (\"" <> SBC.taggedGroupName gtt <> "\") at the same type for " <> show idt <> " row=" <> SBC.dataSetName rtt
        Nothing -> do
          let newRims = DHash.insert rtt (SBC.GroupIndexAndIntMapMakers tf (SBC.GroupIndexMakers $ DHash.insert gtt mkIndex gims) gimbs) rowInfoMakers
          pure (Just newRims, ())

{-
addGroupIndexForModelCrosswalk :: forall k r es . (EffF.Fail :> es, EffS.State (SBC.RowInfoMakers (SBC.DataSource r)) :> es, Typeable k)
                               => SBC.RowTypeTag r
                               -> SBC.MakeIndex r k
                               -> Eff es ()
addGroupIndexForModelCrosswalk rtt mkIndex = do
  let gttX :: SBC.GroupTypeTag k = SBC.GroupTypeTag $ "I_" <> (SBC.dataSetName rtt)
--      idt = inputDataType rtt
  addGroupIndexForData gttX rtt mkIndex
-}
buildIntMapBuilderF :: (k -> Either Text Int) -> (r -> k) -> SBC.DataToIntMap r k --FL.FoldM (Either Text) r (IM.IntMap k)
buildIntMapBuilderF eIntF keyF = SBC.DataToIntMap $ Foldl.FoldM step (return IntMap.empty) return where
  step im r = case eIntF $ keyF r of
    Left msg -> Left $ "Indexing error when trying to build IntMap index: " <> msg
    Right n -> Right $ IntMap.insert n (keyF r) im

dataToIntMapFromFoldable :: forall k r f. (Show k, Ord k, Foldable f) => (r -> k) -> f k -> SBC.DataToIntMap r k
dataToIntMapFromFoldable keyF keys = buildIntMapBuilderF lkUp keyF where
  keysM :: Map k Int = Map.fromList $ zip (Foldl.fold Foldl.list keys) [1..]
  lkUp k = maybe (Left $ "dataToIntMapFromFoldable.lkUp: " <> show k <> " not found ") Right $ Map.lookup k keysM

dataToIntMapFromEnum :: forall k r. (Show k, Enum k, Bounded k, Ord k) => (r -> k) -> SBC.DataToIntMap r k
dataToIntMapFromEnum keyF = dataToIntMapFromFoldable keyF [minBound..maxBound]

dataToIntMapFromKeyedRow :: (r -> k) -> SBC.DataToIntMap r k
dataToIntMapFromKeyedRow key = SBC.DataToIntMap $ Foldl.generalize fld where
  fld = fmap (IntMap.fromList . zip [1..]) $ Foldl.premap key Foldl.list

addGroupIntMapForData :: forall r k es . (EffF.Fail :> es, EffS.State (SBC.RowInfoMakers (SBC.DataSource r)) :> es)
                      => SBC.GroupTypeTag k
                      -> SBC.RowTypeTag r
                      -> SBC.DataToIntMap r k
                      -> Eff es ()
addGroupIntMapForData gtt rtt mkIntMap = withRowInfoMakers @(SBC.DataSource r) f where
  f :: forall x. SBC.RowInfoMakers x -> Eff es (Maybe (SBC.RowInfoMakers x), ())
  f rowInfoMakers = do
    case DHash.lookup rtt rowInfoMakers of
      Nothing -> SBC.buildError
        $ "Data-set \"" <> SBC.dataSetName rtt <> "\" needs to be added before groups can be added to it. Perhaps you have switched the model and GQ types?"
      Just (SBC.GroupIndexAndIntMapMakers tf gims (SBC.GroupIntMapBuilders gimbs)) -> case DHash.lookup gtt gimbs of
        Just _ -> SBC.buildError $ "Attempt to add a second group (\"" <> SBC.taggedGroupName gtt <> "\") at the same type for row=" <> SBC.dataSetName rtt
        Nothing -> do
          let newRims = DHash.insert rtt (SBC.GroupIndexAndIntMapMakers tf gims (SBC.GroupIntMapBuilders $ DHash.insert gtt mkIntMap gimbs)) rowInfoMakers
          pure (Just newRims, ())




withRowInfoMakers :: forall x es y . EffS.State (SBC.RowInfoMakers x) :> es
                  => (forall z. SBC.RowInfoMakers z -> Eff es (Maybe (SBC.RowInfoMakers z), y)) -> Eff es y
withRowInfoMakers f = do
  rims <- EffS.get @(SBC.RowInfoMakers x)
  (mRims, y) <- f rims
  case mRims of
    Nothing -> pure ()
    Just newRims -> EffS.put @(SBC.RowInfoMakers x) newRims
  pure y
