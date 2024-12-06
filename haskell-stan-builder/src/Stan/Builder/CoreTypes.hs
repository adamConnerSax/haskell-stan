{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

module Stan.Builder.CoreTypes
  (
    module Stan.Builder.CoreTypes
  )
where

import qualified Stan.Builder.JSON as SJ
--import Stan.ModelBuilder.Distributions ()

import qualified Stan.Language.Types as SLT
import qualified Stan.Language.Program as SLP
import qualified Stan.Language.Format as SLF
import qualified Stan.Language.Statements as SLS -- was TE
import qualified Stan.Builder.ParameterTypes as SBPT

import Prelude hiding (All)
import qualified Control.Foldl as Foldl
import qualified Data.Aeson as Aeson
--import qualified Data.Array as Array
import qualified Data.Dependent.HashMap as DHash
import qualified Data.GADT.Compare as GADT
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Some as Some
import qualified Data.Text as T
import qualified Data.Hashable as Hashable
import qualified Type.Reflection as Reflection
import qualified Data.GADT.Show as GADT
import qualified Data.Dependent.Sum as DSum
import qualified Data.Dependent.Map as DM
--import Stan.ModelConfig (InputDataType(..))

type FunctionsBlock = T.Text
type DataBlock = T.Text
type TransformedDataBlock = T.Text
type ParametersBlock = T.Text
type TransformedParametersBlock = T.Text
type ModelBlock = T.Text
type GeneratedQuantitiesBlock = T.Text

newtype StanBuilderM md gq a = StanBuilderM { unStanBuilderM :: ExceptT Text (State (BuilderState md gq)) a }
                             deriving newtype (Functor, Applicative, Monad, MonadState (BuilderState md gq))

runStanBuilder :: md
               -> gq
               -> StanGroupBuilderM md gq ()
               -> StanBuilderM md gq a
               -> Either Text (BuilderState md gq, a)
runStanBuilder md gq sgb sb =
  let builderState = runStanGroupBuilder sgb md gq
      (resE, bs) = usingState builderState . runExceptT $ unStanBuilderM sb
  in fmap (bs,) resE

stanBuildError :: Text -> StanBuilderM md gq a
stanBuildError t = do
  builderText <- dumpBuilderState <$> get
  StanBuilderM $ ExceptT (pure $ Left $ t <> "\nBuilder:\n" <> builderText)

stanBuildMaybe :: Text -> Maybe a -> StanBuilderM md gq a
stanBuildMaybe msg = maybe (stanBuildError msg) return

stanBuildEither :: Either Text a -> StanBuilderM md gq a
stanBuildEither = either stanBuildError return

data BuilderState md gq = BuilderState { declaredVars :: !ScopedDeclarations
                                       , indexBindings :: !SLS.IndexLookupCtxt
                                       , modelRowBuilders :: !(RowInfos md)
                                       , gqRowBuilders :: !(RowInfos gq)
                                       , constModelJSON :: JSONSeriesFold ()  -- json for things which are attached to no data set.
                                       , constGQJSON :: JSONSeriesFold ()
                                       , hasFunctions :: !(Set.Set Text)
                                       , parameterCollection :: SBPT.BParameterCollection
                                       , code :: !StanCode
                                       }

initialBuilderState :: RowInfos md -> RowInfos gq -> BuilderState md gq
initialBuilderState modelRowInfos gqRowInfos =
  BuilderState
  initialScopedDeclarations
  SLS.emptyLookupCtxt
  modelRowInfos
  gqRowInfos
  mempty
  mempty
  Set.empty
  (SBPT.BParameterCollection mempty mempty)
  (StanCode SLP.SBData SLP.emptyStanProgram)

dumpBuilderState :: BuilderState md gq -> Text
dumpBuilderState bs = -- (BuilderState dvs ibs ris js hf c) =
  "Declared Vars: " <> show (declaredVars bs)
  <> "\n index-bindings: " <> SLF.printLookupCtxt (indexBindings bs)
  <> "\n model row-info-keys: " <> show (DHash.keys $ modelRowBuilders bs)
  <> "\n gq row-info-keys: " <> show (DHash.keys $ gqRowBuilders bs)
  <> "\n functions: " <> show (hasFunctions bs)
  <> "\n parameterCollection (keys)" <> show (DM.keys $ SBPT.pdm $ parameterCollection bs)

initialScopedDeclarations :: ScopedDeclarations
initialScopedDeclarations = let x = one (DeclarationMap Map.empty)
                            in ScopedDeclarations GlobalScope x x x

type RowInfoMakers d = DHash.DHashMap RowTypeTag (GroupIndexAndIntMapMakers d)
data GroupBuilderS md gq = GroupBuilderS { gbModelS :: RowInfoMakers md, gbGQS :: RowInfoMakers gq}

modifyGBModelS :: (RowInfoMakers md -> RowInfoMakers md) -> GroupBuilderS md gq -> GroupBuilderS md gq
modifyGBModelS f (GroupBuilderS mRims gqRims) = GroupBuilderS (f mRims) gqRims

modifyGBGQS :: (RowInfoMakers gq -> RowInfoMakers gq) -> GroupBuilderS md gq -> GroupBuilderS md gq
modifyGBGQS f (GroupBuilderS mRims gqRims) = GroupBuilderS mRims (f gqRims)

newtype StanGroupBuilderM md gq a
  = StanGroupBuilderM { unStanGroupBuilderM :: ExceptT Text (State (GroupBuilderS md gq)) a }
  deriving newtype (Functor, Applicative, Monad, MonadState (GroupBuilderS md gq))

stanGroupBuildError :: Text -> StanGroupBuilderM md gq a
stanGroupBuildError t = StanGroupBuilderM $ ExceptT (pure $ Left t)

-- This builds the indexes but not the IntMaps.  Those need to be built at the end.
runStanGroupBuilder :: StanGroupBuilderM md gq () -> md -> gq -> BuilderState md gq
runStanGroupBuilder sgb md gq =
  let (_, gbs) = usingState (GroupBuilderS DHash.empty DHash.empty) $ runExceptT $ unStanGroupBuilderM sgb
      modelRowInfos = DHash.mapWithKey (buildRowInfo md) $ gbModelS gbs
      gqRowInfos = DHash.mapWithKey (buildRowInfo gq) $ gbGQS gbs
  in initialBuilderState modelRowInfos gqRowInfos

-- build a new RowInfo from the row index and IntMap builders
buildRowInfo :: d -> RowTypeTag r -> GroupIndexAndIntMapMakers d r -> RowInfo d r
buildRowInfo d rtt (GroupIndexAndIntMapMakers tf@(ToFoldable f) ims imbs) = Foldl.fold fld $ f d  where
  gisFld = indexBuildersForDataSetFold ims
  uBindings = Map.insert (dataSetName rtt) (SLS.namedLIndex ("N_" <> dataSetName rtt))
                $ useBindingsFromGroupIndexMakers rtt ims
  fld = RowInfo tf uBindings <$> gisFld <*> pure imbs <*> pure mempty

useBindingsFromGroupIndexMakers :: RowTypeTag r -> GroupIndexMakers r -> SLS.IndexArrayMap
useBindingsFromGroupIndexMakers rtt (GroupIndexMakers gims) = Map.fromList l where
  l = g <$> DHash.toList gims
  g (gtt DSum.:=> _) =
    let gn = taggedGroupName gtt
        dsn = dataSetName rtt
        indexName = dsn <> "_" <> gn
        indexExpr = SLS.namedLIndex indexName
    in (gn, indexExpr)

intMapsForDataSetFoldM :: GroupIntMapBuilders r -> Foldl.FoldM (Either Text) r (GroupIntMaps r)
intMapsForDataSetFoldM (GroupIntMapBuilders imbs) = GroupIntMaps <$> DHash.traverse unDataToIntMap imbs

indexBuildersForDataSetFold :: GroupIndexMakers r -> Foldl.Fold r (GroupIndexes r)
indexBuildersForDataSetFold (GroupIndexMakers gims) = GroupIndexes <$> DHash.traverse makeIndexMapF gims

mapLookupE :: Ord k => (k -> Text) -> Map k a -> k -> Either Text a
mapLookupE errMsg m k = case Map.lookup k m of
  Just a -> Right a
  Nothing -> Left $ errMsg k

toIntMap :: Map k Int -> IntMap k
toIntMap = IntMap.fromList . fmap (\(a, b) -> (b, a)) . Map.toList

mapToIndexMap :: Ord k => (r -> k) -> Map k Int -> IndexMap r k
mapToIndexMap h m = indxMap where
  lookupK = mapLookupE (const $ "key not found when building given index") m
  intIndex = IntIndex (Map.size m) (lookupK . h)
  indxMap = IndexMap intIndex lookupK (toIntMap m) h

makeIndexMapF :: MakeIndex r k -> Foldl.Fold r (IndexMap r k)
makeIndexMapF (GivenIndex m h) = pure $ mapToIndexMap h m
makeIndexMapF (FoldToIndex fld h) = fmap (mapToIndexMap h) fld

data StanCode = StanCode { curBlock :: SLP.StanBlock
                         , program :: SLP.StanProgram
                         }

data VariableScope = GlobalScope | ModelScope | GQScope deriving stock (Show, Eq, Ord)

newtype DeclarationMap = DeclarationMap (Map SLS.StanName SLT.EType) deriving stock (Show)
data ScopedDeclarations = ScopedDeclarations { currentScope :: VariableScope
                                             , globalScope :: NonEmpty DeclarationMap
                                             , modelScope :: NonEmpty DeclarationMap
                                             , gqScope :: NonEmpty DeclarationMap
                                             } deriving stock (Show)

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

data InputDataType = ModelData | GQData deriving stock (Show, Eq, Ord, Enum, Bounded, Generic)
instance Hashable InputDataType

data JSONSeriesFold row where
  JSONSeriesFold :: SJ.StanJSONF row Aeson.Series -> JSONSeriesFold row

instance Semigroup (JSONSeriesFold row) where
  (JSONSeriesFold a) <> (JSONSeriesFold b) = JSONSeriesFold (a <> b)

instance Monoid (JSONSeriesFold row) where
  mempty = JSONSeriesFold $ pure mempty

-- f is existential here.  We supply the choice when we *construct* a ToFoldable
data ToFoldable d row where
  ToFoldable :: Foldable f => (d -> f row) -> ToFoldable d row

-- key for dependepent map.
data RowTypeTag r where
  RowTypeTag :: Typeable r => InputDataType -> Text -> RowTypeTag r


dataSetName :: RowTypeTag r -> Text
dataSetName (RowTypeTag _ n) = n

inputDataType :: RowTypeTag r -> InputDataType
inputDataType (RowTypeTag idt _) = idt

dataSetSizeName :: RowTypeTag r -> Text
dataSetSizeName rtt = "N_" <> dataSetName rtt

-- we need the empty constructors here to bring in the Typeable constraints in the GADT
instance GADT.GEq RowTypeTag where
  geq rta@(RowTypeTag idt1 n1) rtb@(RowTypeTag idt2 n2) =
    case Reflection.eqTypeRep (Reflection.typeOf rta) (Reflection.typeOf rtb) of
      Just Reflection.HRefl -> if (n1 == n2) && (idt1 == idt2) then Just Reflection.Refl else Nothing
      _ -> Nothing

instance GADT.GShow RowTypeTag where
  gshowsPrec _ (RowTypeTag idt n) s = s ++ "RTT (name=)" ++ toString n ++ "; inputType=" ++ show idt ++ ")"

instance Hashable.Hashable (Some.Some RowTypeTag) where
  hash (Some.Some (RowTypeTag idt n)) = Hashable.hash idt `Hashable.hashWithSalt` n
  hashWithSalt s (Some.Some (RowTypeTag idt n)) = Hashable.hashWithSalt s idt `Hashable.hashWithSalt` n

data GroupTypeTag k where
  GroupTypeTag :: Typeable k => Text -> GroupTypeTag k

taggedGroupName :: GroupTypeTag k -> Text
taggedGroupName (GroupTypeTag n) = n

groupSizeName :: GroupTypeTag k -> Text
groupSizeName g = "J_" <> taggedGroupName g

dataByGroupIndexName :: RowTypeTag r -> GroupTypeTag g -> Text
dataByGroupIndexName rtt gtt = dataSetName rtt <> "_" <> taggedGroupName gtt

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
type DataSetGroupIntMaps = DHash.DHashMap RowTypeTag GroupIntMaps

displayDataSetGroupIntMaps :: DataSetGroupIntMaps -> Text
displayDataSetGroupIntMaps = DHash.foldrWithKey g ""
  where
--    h = DHash.foldrWithKey (\gtt _ t -> t <> ", " <> taggedGroupName gtt) ""
    g rtt gims {-(GroupIntMaps gim)-} t = t <> "rtt=" <> dataSetName rtt <> " (idt=" <> show (inputDataType rtt) <> "): " <> displayGroupIntMaps gims <> "\n"

displayGroupIntMaps :: GroupIntMaps k -> Text
displayGroupIntMaps (GroupIntMaps gim) = h gim where
  h = DHash.foldrWithKey (\gtt _ t -> t <> ", " <> taggedGroupName gtt) ""

data GroupIndexAndIntMapMakers d r = GroupIndexAndIntMapMakers (ToFoldable d r) (GroupIndexMakers r) (GroupIntMapBuilders r)

data IndexMap r k = IndexMap
                    { rowToGroupIndex :: IntIndex r,
                      groupKeyToGroupIndex :: k -> Either Text Int,
                      groupIndexToGroupKey :: IntMap.IntMap k,
                      rowToGroup :: r -> k
                    }

contraIndexMap :: (a -> b) -> IndexMap b k -> IndexMap a k
contraIndexMap f (IndexMap rgi ggi gigk rg) = IndexMap (contramap f rgi) ggi gigk (rg . f)

data RowInfo d r = RowInfo
                   {
                     toFoldable    :: ToFoldable d r
                   , expressionBindings :: SLS.IndexArrayMap
                   , groupIndexes  :: GroupIndexes r
                   , groupIntMapBuilders  :: GroupIntMapBuilders r
                   , jsonSeries    :: JSONSeriesFold r
                   }

-- the key is a name for the data-set.  The tag carries the toDataSet function
type RowBuilder d = DSum.DSum RowTypeTag (RowInfo d)
type RowInfos d = DHash.DHashMap RowTypeTag (RowInfo d)
