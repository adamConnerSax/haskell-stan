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

import qualified Stan.Language as SL
import qualified Stan.Builder.Core as SBC
import qualified Stan.Builder.Build as SBB
import qualified Stan.Builder.JSON as SBJ

import Prelude hiding (All)
import qualified Control.Foldl as Foldl
import qualified Data.Dependent.HashMap as DHash
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import Effectful (Eff)
import qualified Effectful.State.Static.Local as EffS
import Stan.Builder.Core (StanDataBuildersC)

type AddGroup k i d es = (Typeable k, SBC.StanConstJsonC i d es)

addGroup :: forall k i d es . AddGroup k i d es
         => SBC.InputDataType i d -> Text -> Int -> Eff es (SBC.GroupTypeTag k, SL.IntE)
addGroup idt groupName size = do
  lE <- SBJ.addFixedIntJson SBJ.ErrIfDuplicate idt ("J_" <> groupName) (Just 1) size
  pure (SBC.GroupTypeTag groupName, lE)

addEnumGroup :: forall k i d es . (Enum k, Bounded k, AddGroup k i d es)
             => SBC.InputDataType i d -> Text
             -> Eff es (SBC.GroupTypeTag k, SL.IntE)
addEnumGroup idt groupName = addGroup @k idt groupName size
  where
    size = Foldl.fold Foldl.length $ ([minBound..maxBound] :: [k])

addGroupFromCollection :: forall k i d f es . (Ord k, Foldable f, AddGroup k i d es)
                       => SBC.InputDataType i d -> Text -> f k -> Eff es (SBC.GroupTypeTag k, SL.IntE)
addGroupFromCollection idt groupName c = addGroup @_ idt groupName size
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


addGroupIndexForData :: forall i d r k es . (SBC.StanDataBuildersC i d es)
                     => SBC.InputDataType i d
                     -> SBC.GroupTypeTag k
                     -> SBC.RowTypeTag r
                     -> SBC.MakeIndex r k
                     -> Eff es ()
addGroupIndexForData idt gtt rtt mkIndex = withRowInfoMakers @i f where
  f :: SBC.RowInfoMakers i d -> Eff es (Maybe (SBC.RowInfoMakers i d), ())
  f rowInfoMakers = do
    case DHash.lookup rtt $ SBC.unRowInfoMakers rowInfoMakers of
      Nothing -> SBC.buildError $ "Data-set \"" <> SBC.dataSetName rtt <> "\" needs to be added to " <> show idt <> " before groups can be added to it."
      Just (SBC.GroupIndexAndIntMapMakers tf (SBC.GroupIndexMakers gims) gimbs) -> case DHash.lookup gtt gims of
        Just _ -> SBC.buildError
                  $ "Attempt to add a second group (\"" <> SBC.taggedGroupName gtt <> "\") at the same type for " <> show idt <> " row=" <> SBC.dataSetName rtt
        Nothing -> do
          let newRims = SBC.RowInfoMakers
                        $ DHash.insert rtt (SBC.GroupIndexAndIntMapMakers tf (SBC.GroupIndexMakers $ DHash.insert gtt mkIndex gims) gimbs)
                        $ SBC.unRowInfoMakers rowInfoMakers
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

addGroupIntMapForData :: forall i d r k es . StanDataBuildersC i d es
                      => SBC.InputDataType i d
                      -> SBC.GroupTypeTag k
                      -> SBC.RowTypeTag r
                      -> SBC.DataToIntMap r k
                      -> Eff es ()
addGroupIntMapForData _idt gtt rtt mkIntMap = withRowInfoMakers f where
  f :: SBC.RowInfoMakers i d -> Eff es (Maybe (SBC.RowInfoMakers i d), ())
  f rowInfoMakers = do
    case DHash.lookup rtt $ SBC.unRowInfoMakers rowInfoMakers of
      Nothing -> SBC.buildError
        $ "Data-set \"" <> SBC.dataSetName rtt <> "\" needs to be added before groups can be added to it. Perhaps you have switched the model and GQ types?"
      Just (SBC.GroupIndexAndIntMapMakers tf gims (SBC.GroupIntMapBuilders gimbs)) -> case DHash.lookup gtt gimbs of
        Just _ -> SBC.buildError $ "Attempt to add a second group (\"" <> SBC.taggedGroupName gtt <> "\") at the same type for row=" <> SBC.dataSetName rtt
        Nothing -> do
          let newRims = SBC.RowInfoMakers
                        $ DHash.insert rtt (SBC.GroupIndexAndIntMapMakers tf gims (SBC.GroupIntMapBuilders $ DHash.insert gtt mkIntMap gimbs))
                        $ SBC.unRowInfoMakers rowInfoMakers
          pure (Just newRims, ())

withRowInfoMakers :: forall i d es y . SBC.StanDataBuildersC i d es
                  => (SBC.RowInfoMakers i d -> Eff es (Maybe (SBC.RowInfoMakers i d), y)) -> Eff es y
withRowInfoMakers f = do
  rims <- EffS.get @(SBC.RowInfoMakers i d)
  (mRims, y) <- f rims
  case mRims of
    Nothing -> pure ()
    Just newRims -> EffS.put @(SBC.RowInfoMakers i d) newRims
  pure y

indexMap :: forall i d r k es . SBC.StanRowInfoC i d es
         => SBC.InputDataType i d -> SBC.RowTypeTag r -> SBC.GroupTypeTag k -> Eff es (SBC.IndexMap r k)
indexMap idt rtt gtt = SBB.withRowInfo err f idt rtt where
  err = SBC.buildError $ "ModelBuilder.indexMap: \"" <> SBC.dataSetName rtt <> "\" not present in row builders."
  f :: forall x. SBC.RowInfo x r -> Eff es (SBC.IndexMap r k)
  f rowInfo = do
    case DHash.lookup gtt ((\(SBC.GroupIndexes x) -> x) $ SBC.groupIndexes rowInfo) of
      Nothing -> SBC.buildError
                 $ "ModelBuilder.indexMap: \""
                 <> SBC.taggedGroupName gtt
                 <> "\" not present in indexes for \""
                 <> SBC.dataSetName rtt
      Just im -> return im

getGroupIndex :: forall r k.
                 SBC.RowTypeTag r
              -> SBC.GroupTypeTag k
              -> SBC.DataSetGroupIntMaps
              -> Either Text (IntMap k)
getGroupIndex rtt gtt dsgi@(SBC.DataSetGroupIntMaps grpIndexes) =
  case DHash.lookup rtt grpIndexes of
    Nothing -> Left
               $ "getGroupIndex: " <> SBC.dataSetName rtt <> " not found in data-set group int maps: "
               <> SBC.displayDataSetGroupIntMaps dsgi <> "."
               <> " If this error is complaining about a data-set key that appears to be present, double check the *types* used when constructing the row-type-tags"

    Just gims@(SBC.GroupIntMaps gim) -> case DHash.lookup gtt gim of
      Nothing -> Left $ "getGroupIndex: \"" <> SBC.taggedGroupName gtt
                 <> "\" not found in Group int maps ("
                 <> SBC.displayGroupIntMaps gims <> ") for data-set \"" <> SBC.dataSetName rtt <> "\""
      Just im -> Right im

groupIndexVarName :: SBC.RowTypeTag r -> SBC.GroupTypeTag k -> SL.VarName
groupIndexVarName rtt gtt = SBC.dataSetName rtt <> "_" <> SBC.taggedGroupName gtt
{-# INLINEABLE groupIndexVarName #-}

getGroupIndexVar :: forall i d r k es. SBC.StanRowInfoC i d es
                 => SBC.InputDataType i d
                 -> SBC.RowTypeTag r
                 -> SBC.GroupTypeTag k
                 -> Eff es (SL.UExpr SL.EIndexArray)
getGroupIndexVar idt rtt gtt = do
  let vName = groupIndexVarName rtt gtt
      dsNotFoundErr = SBC.buildError
                      $ "getGroupIndexVar: data-set=" <> SBC.dataSetName rtt <> " (input type=" <> show idt <> ") not found."
      varIfGroup :: forall x d1 . SBC.RowInfo d1 x -> Eff es (SL.UExpr SL.EIndexArray)
      varIfGroup ri =
        let (SBC.GroupIndexes gis) = SBC.groupIndexes ri
        in case DHash.lookup gtt gis of
          Just _ -> return $ SL.namedE vName SL.sIndexArray --SME.StanVar varName (SME.StanArray [SME.NamedDim $ dataSetName rtt] SME.StanInt)
          Nothing -> SBC.buildError
            $ "getGroupIndexVar: group=" <> SBC.taggedGroupName gtt
            <> " not found in data-set=" <> SBC.dataSetName rtt <> " (input type=" <> show idt <> ") not found."
  SBB.withRowInfo dsNotFoundErr varIfGroup idt rtt
