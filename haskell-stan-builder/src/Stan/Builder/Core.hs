{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Stan.Builder.Core
  (
    module Stan.Builder.Core
  )
where

import qualified Stan.Builder.JSON.JSONUtils as SJ
import qualified Stan.Language.Types as SLT
import qualified Stan.Language.Program as SLP
import qualified Stan.Language.Expression as SLE
import qualified Stan.Language.Expressions as SLE
import qualified Stan.Builder.Parameters.Types as SBPT

import Prelude hiding (All)
import qualified Control.Foldl as Foldl
import qualified Data.Aeson as Aeson
import qualified Data.Dependent.HashMap as DHash
import qualified Data.GADT.Compare as GADT
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import qualified Data.Some as Some
import qualified Data.Text as T
import qualified Data.Hashable as Hashable
import qualified Type.Reflection as Reflection
import qualified Data.GADT.Show as GADT
import qualified Data.Dependent.Sum as DSum
import qualified Data.Dependent.Map as DM

import Effectful ((:>), Eff)
import qualified Effectful.State.Static.Local as EffS
import qualified Effectful.Writer.Static.Local as EffW
import qualified Effectful.Fail as EffF
import qualified Effectful.Dispatch.Dynamic as EffD


type FunctionsBlock = T.Text
type DataBlock = T.Text
type TransformedDataBlock = T.Text
type ParametersBlock = T.Text
type TransformedParametersBlock = T.Text
type ModelBlock = T.Text
type GeneratedQuantitiesBlock = T.Text

type family DataSource (i :: InputDataT) :: Type
type ModelSource = DataSource ModelDataT
type GQSource = DataSource GQDataT

--type family SourceType (i :: InputDataT) :: Type

data InputDataType (i :: InputDataT) where
  ModelData :: InputDataType ModelDataT
  GQData :: InputDataType GQDataT

deriving stock instance Eq (InputDataType i)
deriving stock instance Show (InputDataType i)

instance Hashable (InputDataType i) where
  hashWithSalt n ModelData = hashWithSalt n ModelDataT
  hashWithSalt n GQData = hashWithSalt n GQDataT

inputDataT :: InputDataType i -> InputDataT
inputDataT ModelData = ModelDataT
inputDataT GQData = GQDataT

caseInputDataType :: a -> a -> InputDataType i -> a
caseInputDataType aModel aGQ = \case
  ModelData -> aModel
  GQData -> aGQ

type RowInfoMakers i = DHash.DHashMap (RowTypeTag i) (GroupIndexAndIntMapMakers (DataSource i))


newtype FunctionNames = FunctionNames { unFunctionNames :: Set.Set SLT.FunctionName } deriving newtype (Show)
newtype JSONNames = JSONNames { unJSONNames :: Set.Set Text } deriving newtype (Show)
type BuildLog = Seq.Seq Text

type GroupBuilderS (i :: InputDataT) = EffS.State (RowInfoMakers i)

type StanBuilderEffs =
  [
    EffS.State (RowInfos ModelDataT)
  , EffS.State (RowInfos GQDataT)
  , EffS.State SBPT.BParameterCollection
  , EffS.State StanCode
  , EffS.State FunctionNames
  , EffS.State (JSONConstFold ModelDataT)
  , EffS.State (JSONConstFold GQDataT)
  , EffS.State JSONNames
  , EffW.Writer BuildLog
  , EffF.Fail
  ]

type StanFail es = EffF.Fail :> es
type StanBuildLogC es = (StanFail es, EffW.Writer BuildLog :> es)
type StanCodeC es = (StanBuildLogC es, EffS.State StanCode :> es)
type StanFunctionsC es = (StanCodeC es, EffS.State FunctionNames :> es)
type StanParametersC es = (StanBuildLogC es, EffS.State SBPT.BParameterCollection :> es)
type StanGroupC i es = (StanBuildLogC es, EffS.State (RowInfoMakers i) :> es)
type StanRowInfoC i es = (StanBuildLogC es, EffS.State (RowInfos i) :> es)
type StanJsonC i es = (StanRowInfoC i es, StanCodeC es, EffS.State JSONNames :> es)
type StanConstJsonC i es = (StanCodeC es, EffS.State JSONNames :> es, EffS.State (JSONConstFold i) :> es)

type StanDataBuilderEff i = Eff '[GroupBuilderS i
                                 , EffS.State StanCode
                                 , EffS.State (JSONConstFold i)
                                 , EffS.State JSONNames
                                 , EffW.Writer BuildLog
                                 , EffF.Fail]
type StanModelBuilderEff = Eff StanBuilderEffs

type StateAndFailEff s es = (EffS.State s :> es, EffF.Fail :> es)

buildLog :: EffW.Writer (Seq.Seq Text) :> es => Text -> Eff es ()
buildLog = EffW.tell . Seq.singleton

buildError :: EffF.Fail :> es => Text -> Eff es a
buildError = EffD.send . EffF.Fail . toString

buildMaybe :: EffF.Fail :> es => Text -> Maybe a -> Eff es a
buildMaybe msg = maybe (buildError msg) pure

buildEither :: EffF.Fail :> es => Either Text a -> Eff es a
buildEither = either buildError pure

data BuilderState = BuilderState { --declaredVars :: !ScopedDeclarations
--                                       , indexBindings :: !SLA.IndexLookupCtxt
  modelRowBuilders :: !(RowInfos ModelDataT)
  , gqRowBuilders :: !(RowInfos GQDataT)
  , constModelJSON :: JSONConstFold ModelDataT  -- json for things which are attached to no data set.
  , constGQJSON :: JSONConstFold GQDataT
  , hasFunctions :: !(Set.Set Text)
  , parameterCollection :: SBPT.BParameterCollection
  , code :: !StanCode
  }

initialBuilderState :: RowInfos ModelDataT -> RowInfos GQDataT -> BuilderState
initialBuilderState modelRowInfos gqRowInfos =
  BuilderState
--  initialScopedDeclarations
--  SLA.emptyIndexLookupCtxt
  modelRowInfos
  gqRowInfos
  mempty
  mempty
  Set.empty
  (SBPT.BParameterCollection mempty mempty)
  (StanCode SLP.SBData SLP.emptyStanProgram)

dumpBuilderState :: BuilderState -> Text
dumpBuilderState bs = -- (BuilderState dvs ibs ris js hf c) =
--  "Declared Vars: " <> show (declaredVars bs)
--  <> "\n index-bindings: " <> SLF.printLookupCtxt (indexBindings bs)
  "\n model row-info-keys: " <> show (DHash.keys $ modelRowBuilders bs)
  <> "\n gq row-info-keys: " <> show (DHash.keys $ gqRowBuilders bs)
  <> "\n functions: " <> show (hasFunctions bs)
  <> "\n parameterCollection (keys)" <> show (DM.keys $ SBPT.pdm $ parameterCollection bs)


intMapsForDataSetFoldM :: GroupIntMapBuilders r -> Foldl.FoldM (Either Text) r (GroupIntMaps r)
intMapsForDataSetFoldM (GroupIntMapBuilders imbs) = GroupIntMaps <$> DHash.traverse unDataToIntMap imbs

data StanCode = StanCode { curBlock :: SLP.StanBlock
                         , program :: SLP.StanProgram
                         }

data StanModel = StanModel
  { functionsBlock :: Maybe FunctionsBlock,
    dataBlock :: DataBlock,
    dataBlockGQ :: DataBlock,
    transformedDataBlockM :: Maybe TransformedDataBlock,
    transformedDataBlockMGQ :: Maybe TransformedDataBlock,
    parametersBlock :: ParametersBlock,
    transformedParametersBlockM :: Maybe TransformedParametersBlock,
    modelBlock :: ModelBlock,
    generatedQuantitiesBlockM :: Maybe GeneratedQuantitiesBlock,
    genLogLikelihoodBlock :: GeneratedQuantitiesBlock
  }
  deriving stock (Show, Eq, Ord)

data InputDataT = ModelDataT | GQDataT deriving stock (Show, Eq, Ord, Enum, Bounded, Generic)
instance Hashable InputDataT

data JSONSeriesFold row where
  JSONSeriesFold :: SJ.StanJSONF row Aeson.Series -> JSONSeriesFold row

instance Semigroup (JSONSeriesFold row) where
  (JSONSeriesFold a) <> (JSONSeriesFold b) = JSONSeriesFold (a <> b)

instance Monoid (JSONSeriesFold row) where
  mempty = JSONSeriesFold $ pure mempty

data JSONConstFold (i :: InputDataT) where
  JSONConstFold :: SJ.StanJSONF () Aeson.Series -> JSONConstFold i

instance Semigroup (JSONConstFold i) where
  (JSONConstFold a) <> (JSONConstFold b) = JSONConstFold (a <> b)

instance Monoid (JSONConstFold i) where
  mempty = JSONConstFold $ pure mempty


-- f is existential here.  We supply the choice when we *construct* a ToFoldable
data ToFoldable d row where
  ToFoldable :: Foldable f => (d -> f row) -> ToFoldable d row

-- key for dependepent map.
data RowTypeTag (i :: InputDataT) r where
  RowTypeTag :: (Typeable i, Typeable r) => InputDataType i -> Text -> RowTypeTag i r

dataSetName :: RowTypeTag i r -> Text
dataSetName (RowTypeTag _ n) = n

dataSetInputData :: RowTypeTag i r -> InputDataType i
dataSetInputData (RowTypeTag idt _) = idt

-- we need the empty constructors here to bring in the Typeable constraints in the GADT
instance GADT.GEq (RowTypeTag i) where
  geq rta@(RowTypeTag idt1 n1) rtb@(RowTypeTag idt2 n2) =
    case Reflection.eqTypeRep (Reflection.typeOf rta) (Reflection.typeOf rtb) of
      Just Reflection.HRefl -> if (n1 == n2) && (idt1 == idt2) then Just Reflection.Refl  else Nothing
      _ -> Nothing

instance GADT.GShow (RowTypeTag i) where
  gshowsPrec _ (RowTypeTag idt n) s = s ++ "RTT (name=)" ++ toString n ++ "; inputType=" ++ show idt ++ ")"

instance Hashable.Hashable (Some.Some (RowTypeTag i)) where
  hash (Some.Some (RowTypeTag idt n)) = Hashable.hash idt `Hashable.hashWithSalt` n
  hashWithSalt s (Some.Some (RowTypeTag idt n)) = Hashable.hashWithSalt s idt `Hashable.hashWithSalt` n

data GroupTypeTag k where
  GroupTypeTag :: Typeable k => Text -> GroupTypeTag k

{-
groupIndexVarName :: RowTypeTag i r -> GroupTypeTag k -> SLT.VarName
groupIndexVarName rtt gtt = dataSetName rtt <> "_" <> taggedGroupName gtt
{-# INLINEABLE groupIndexVarName #-}
-}
taggedGroupName :: GroupTypeTag k -> Text
taggedGroupName (GroupTypeTag n) = n

groupSizeName :: GroupTypeTag k -> Text
groupSizeName g = "J_" <> taggedGroupName g

groupSizeE :: GroupTypeTag k -> SLE.IntE
groupSizeE gtt = SLE.namedE (groupSizeName gtt) SLT.SInt


dataByGroupIndexName :: RowTypeTag i r -> GroupTypeTag g -> Text
dataByGroupIndexName rtt gtt = dataSetName rtt <> "_" <> taggedGroupName gtt

dataByGroupIndexE :: RowTypeTag i r -> GroupTypeTag k -> SLE.UExpr SLT.EIndexArray
dataByGroupIndexE rtt gtt = SLE.namedE (dataByGroupIndexName rtt gtt) SLT.sIndexArray

-- should depend on length expressions as well. FIX
instance GADT.GEq GroupTypeTag where
  geq gta@(GroupTypeTag n1) gtb@(GroupTypeTag n2) =
    case Reflection.eqTypeRep (Reflection.typeOf gta) (Reflection.typeOf gtb) of
      Just Reflection.HRefl -> if n1 == n2 then Just Reflection.Refl else Nothing
      _ -> Nothing

instance GADT.GShow GroupTypeTag where
  gshowsPrec _ (GroupTypeTag n) s = s ++ "GTT (name= " ++ toString n ++ ")"

instance Hashable.Hashable (Some.Some GroupTypeTag) where
  hash (Some.Some (GroupTypeTag n)) = Hashable.hash n
  hashWithSalt m (Some.Some (GroupTypeTag n)) = hashWithSalt m n

data IntIndex row = IntIndex { i_Size :: Int, i_Index :: row -> Either Text Int }

instance Contravariant IntIndex where
  contramap f (IntIndex s g) = IntIndex s (g . f)

data MakeIndex r k where
  GivenIndex :: Ord k => Map k Int -> (r -> k) -> MakeIndex r k
  FoldToIndex :: Ord k =>  (Foldl.Fold r (Map k Int)) -> (r -> k) -> MakeIndex r k
--  SupplementalIndex :: (Ord k, Foldable f) => f k -> MakeIndex r k

contraMakeIndex :: (a -> b) -> MakeIndex b k -> MakeIndex a k
contraMakeIndex f (GivenIndex m g) = GivenIndex m (g . f)
contraMakeIndex f (FoldToIndex fld g) = FoldToIndex (Foldl.premap f fld) (g . f)

-- Index makers for one row type
newtype GroupIndexMakers r = GroupIndexMakers (DHash.DHashMap GroupTypeTag (MakeIndex r))
-- Indexes for one row type, made using the IndexMaker in GroupIndexMakerDHM and the rows of r from d
newtype GroupIndexes r = GroupIndexes (DHash.DHashMap GroupTypeTag (IndexMap r))

newtype DataToIntMap r k = DataToIntMap { unDataToIntMap :: Foldl.FoldM (Either Text) r (IntMap k) }

contraDataToIntMap :: (a -> b) -> DataToIntMap b k -> DataToIntMap a k
contraDataToIntMap f (DataToIntMap fldM) = DataToIntMap $ Foldl.premapM (pure . f) fldM

newtype GroupIntMapBuilders r = GroupIntMapBuilders (DHash.DHashMap GroupTypeTag (DataToIntMap r))

-- r is a Phantom type here
newtype GroupIntMaps r = GroupIntMaps (DHash.DHashMap GroupTypeTag IntMap.IntMap)
newtype DataSetGroupIntMaps (i :: InputDataT) = DataSetGroupIntMaps { unDataSetGroupIntMaps :: DHash.DHashMap (RowTypeTag i) GroupIntMaps }

displayDataSetGroupIntMaps :: DataSetGroupIntMaps i -> Text
displayDataSetGroupIntMaps = DHash.foldrWithKey g "" . unDataSetGroupIntMaps
  where
    g rtt gims t = t <> "rtt=" <> dataSetName rtt <> " (idt=" <> show (dataSetInputData rtt) <> "): " <> displayGroupIntMaps gims <> "\n"

displayGroupIntMaps :: GroupIntMaps k -> Text
displayGroupIntMaps (GroupIntMaps gim) = h gim where
  h = DHash.foldrWithKey (\gtt _im t -> t <> ", " <> taggedGroupName gtt) ""

data GroupIndexAndIntMapMakers d r where
  GroupIndexAndIntMapMakers :: ToFoldable d r
                            -> GroupIndexMakers r
                            -> GroupIntMapBuilders r
                            -> GroupIndexAndIntMapMakers d r
data IndexMap r k = IndexMap
                    { rowToGroupIndex :: IntIndex r,
                      groupKeyToGroupIndex :: k -> Either Text Int,
                      groupIndexToGroupKey :: IntMap.IntMap k,
                      rowToGroup :: r -> k
                    }

contraIndexMap :: (a -> b) -> IndexMap b k -> IndexMap a k
contraIndexMap f (IndexMap rgi ggi gigk rg) = IndexMap (contramap f rgi) ggi gigk (rg . f)

data RowInfo d r where
  RowInfo :: ToFoldable d r
          -> GroupIndexes r
          -> GroupIntMapBuilders r
          -> JSONSeriesFold r
          -> RowInfo d r

toFoldable :: RowInfo d r -> ToFoldable d r
toFoldable (RowInfo tf _ _ _) = tf

groupIndexes :: RowInfo d r -> GroupIndexes r
groupIndexes (RowInfo _ gi _ _) = gi

groupIntMapBuilders :: RowInfo d r -> GroupIntMapBuilders r
groupIntMapBuilders (RowInfo _ _ gimb _) = gimb

intMapsFromRowInfos :: RowInfos i -> DataSource i -> Either Text (DataSetGroupIntMaps i)
intMapsFromRowInfos rowInfos d =
  let f :: d -> RowInfo d r -> Either Text (GroupIntMaps r)
      f d' (RowInfo (ToFoldable h) _ gims _) = Foldl.foldM (intMapsForDataSetFoldM gims) (h d')
  in DataSetGroupIntMaps <$> DHash.traverse (f d) rowInfos

jsonSeries :: RowInfo d r -> JSONSeriesFold r
jsonSeries (RowInfo _ _ _ jsf) = jsf

-- the key is a name for the data-set.  The tag carries the toDataSet function
type RowBuilder i = DSum.DSum (RowTypeTag i) (RowInfo (DataSource i))
type RowInfos i = DHash.DHashMap (RowTypeTag i) (RowInfo (DataSource i))
