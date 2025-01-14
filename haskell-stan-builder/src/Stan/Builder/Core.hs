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
{-
class InputDataTypeT a where
  inputDataTypeT :: InputDataT

instance InputDataTypeT (InputDataTypeT i) where
  inputDataTypeT = ModelDataT

instance InputDataTypeT GQData  where
  inputDataTypeT = GQDataT
-}
--data ConstJsonFolds = ConstJsonFolds { modelCJ :: JSONSeriesFold (), gqCJ :: JSONSeriesFold () }

type RowInfoMakers i d = DHash.DHashMap (RowTypeTag i) (GroupIndexAndIntMapMakers d)


newtype FunctionNames = FunctionNames { unFunctionNames :: Set.Set SLT.FunctionName } deriving newtype (Show)
newtype JSONNames = JSONNames { unJSONNames :: Set.Set Text } deriving newtype (Show)

type StanBuilderEffs md gq =
  [ EffS.State (RowInfoMakers ModelDataT md)
  , EffS.State (RowInfos ModelDataT md)
  , EffS.State (RowInfoMakers GQDataT gq)
  , EffS.State (RowInfos GQDataT gq)
  , EffS.State SBPT.BParameterCollection
  , EffS.State StanCode
  , EffS.State FunctionNames
  , EffS.State (JSONConstFold md)
  , EffS.State (JSONConstFold gq)
  , EffS.State JSONNames
  , EffW.Writer (Seq.Seq Text)
  , EffF.Fail
  ]


type StanBuildLogC es = EffW.Writer (Seq.Seq Text) :> es
type StanCodeC es = (EffF.Fail :> es, EffS.State StanCode :> es)
type StanFunctionsC es = (StanCodeC es, EffS.State (Set Text) :> es)
type StanParametersC es = (EffS.State SBPT.BParameterCollection :> es, EffF.Fail :> es)

type StanBuilderEff md gq a = Eff (StanBuilderEffs md gq) a


type StateAndFailEff s es = (EffS.State s :> es, EffF.Fail :> es)

buildLog :: EffW.Writer (Seq.Seq Text) :> es => Text -> Eff es ()
buildLog = EffW.tell . Seq.singleton

buildError :: EffF.Fail :> es => Text -> Eff es a
buildError = EffD.send . EffF.Fail . toString

buildMaybe :: EffF.Fail :> es => Text -> Maybe a -> Eff es a
buildMaybe msg = maybe (buildError msg) pure

buildEither :: EffF.Fail :> es => Either Text a -> Eff es a
buildEither = either buildError pure

data BuilderState md gq = BuilderState { --declaredVars :: !ScopedDeclarations
--                                       , indexBindings :: !SLA.IndexLookupCtxt
  modelRowBuilders :: !(RowInfos ModelDataT md)
  , gqRowBuilders :: !(RowInfos GQDataT gq)
  , constModelJSON :: JSONConstFold md  -- json for things which are attached to no data set.
  , constGQJSON :: JSONConstFold gq
  , hasFunctions :: !(Set.Set Text)
  , parameterCollection :: SBPT.BParameterCollection
  , code :: !StanCode
  }

initialBuilderState :: RowInfos ModelDataT md -> RowInfos GQDataT gq -> BuilderState md gq
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

dumpBuilderState :: BuilderState md gq -> Text
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

data JSONConstFold d where
  JSONConstFold :: SJ.StanJSONF () Aeson.Series -> JSONConstFold d

instance Semigroup (JSONConstFold d) where
  (JSONConstFold a) <> (JSONConstFold b) = JSONConstFold (a <> b)

instance Monoid (JSONConstFold d) where
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
  GroupTypeTag :: Typeable k => Text -> SLE.IntE -> GroupTypeTag k

groupIndexVarName :: RowTypeTag i r -> GroupTypeTag k -> SLT.VarName
groupIndexVarName rtt gtt = dataSetName rtt <> "_" <> taggedGroupName gtt
{-# INLINEABLE groupIndexVarName #-}

taggedGroupName :: GroupTypeTag k -> Text
taggedGroupName (GroupTypeTag n _lE) = n

groupSizeName :: GroupTypeTag k -> Text
groupSizeName g = "J_" <> taggedGroupName g

groupSizeE :: GroupTypeTag k -> SLE.IntE
groupSizeE (GroupTypeTag _ lE) = lE

--addEnumGroup :: (Enum k, Bounded k) => (EffS.State StanCode )Text -> GroupTypeTag k
--addEnumGroup name size = GroupTypeTag name (TE.namedE ""size $ intE size)

dataByGroupIndexName :: RowTypeTag i r -> GroupTypeTag g -> Text
dataByGroupIndexName rtt gtt = dataSetName rtt <> "_" <> taggedGroupName gtt

-- should depend on length expressions as well. FIX
instance GADT.GEq GroupTypeTag where
  geq gta@(GroupTypeTag n1 _lE1) gtb@(GroupTypeTag n2 _lE2) =
    case Reflection.eqTypeRep (Reflection.typeOf gta) (Reflection.typeOf gtb) of
      Just Reflection.HRefl -> if n1 == n2 then Just Reflection.Refl else Nothing
      _ -> Nothing

instance GADT.GShow GroupTypeTag where
  gshowsPrec _ (GroupTypeTag n _) s = s ++ "GTT (name= " ++ toString n ++ ")"

instance Hashable.Hashable (Some.Some GroupTypeTag) where
  hash (Some.Some (GroupTypeTag n _)) = Hashable.hash n
  hashWithSalt m (Some.Some (GroupTypeTag n _)) = hashWithSalt m n

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
type DataSetGroupIntMaps i = DHash.DHashMap (RowTypeTag i) GroupIntMaps

displayDataSetGroupIntMaps :: DataSetGroupIntMaps i -> Text
displayDataSetGroupIntMaps = DHash.foldrWithKey g ""
  where
    g rtt gims t = t <> "rtt=" <> dataSetName rtt <> " (idt=" <> show (dataSetInputData rtt) <> "): " <> displayGroupIntMaps gims <> "\n"

displayGroupIntMaps :: GroupIntMaps k -> Text
displayGroupIntMaps (GroupIntMaps gim) = h gim where
  h = DHash.foldrWithKey (\gtt _im t -> t <> ", " <> taggedGroupName gtt) ""

data GroupIndexAndIntMapMakers d r where
  GroupIndexAndIntMapMakers :: {- DataSource r ~ d
                            =>-} ToFoldable d r
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
  RowInfo :: {- DataSource r ~ d
          => -}ToFoldable d r
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

intMapsFromRowInfos :: RowInfos i d -> d -> Either Text (DataSetGroupIntMaps i)
intMapsFromRowInfos rowInfos d =
  let f :: d -> RowInfo d r -> Either Text (GroupIntMaps r)
      f d' (RowInfo (ToFoldable h) _ gims _) = Foldl.foldM (intMapsForDataSetFoldM gims) (h d')
  in DHash.traverse (f d) rowInfos

jsonSeries :: RowInfo d r -> JSONSeriesFold r
jsonSeries (RowInfo _ _ _ jsf) = jsf

-- the key is a name for the data-set.  The tag carries the toDataSet function
type RowBuilder i d = DSum.DSum (RowTypeTag i) (RowInfo d)
type RowInfos i d = DHash.DHashMap (RowTypeTag i) (RowInfo d)
