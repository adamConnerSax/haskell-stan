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
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
module Stan.ModelBuilder.BuildingBlocks.GroupAlpha
  (
    module Stan.ModelBuilder.BuildingBlocks.GroupAlpha
  )
where


import qualified Stan.ModelBuilder.TypedExpressions.Types as TE
import Stan.ModelBuilder.TypedExpressions.TypedList (TypedList(..))
import qualified Stan.ModelBuilder.TypedExpressions.Statements as TE
import qualified Stan.ModelBuilder.TypedExpressions.Indexing as TE
import qualified Stan.ModelBuilder.TypedExpressions.Operations as TE
import qualified Stan.ModelBuilder.TypedExpressions.Functions as TE
import qualified Stan.ModelBuilder.TypedExpressions.StanFunctions as SF
import qualified Stan.ModelBuilder.TypedExpressions.DAG as DAG
import qualified Stan.ModelBuilder.TypedExpressions.DAGTypes as DAG
import qualified Stan.ModelBuilder as SB
import qualified Stan.ModelBuilder.BuildingBlocks as SBB
import qualified Stan.ModelBuilder.Distributions as SMD
import qualified Stan.Parameters as SP

import qualified CmdStan.Types as CS

import Prelude hiding (sum, All)
import qualified Data.List as List
import qualified Data.Dependent.Sum as DSum
import qualified Data.Some as Some
import qualified Data.Dependent.HashMap as DHash
import qualified Data.IntMap as IntMap
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as VU
import qualified Stan.ModelConfig as SB
import Stan.ModelBuilder.BuilderTypes (dataSetSizeName)

import qualified Data.Vec.Lazy as Vec
import qualified Data.Type.Nat as DT

import qualified GHC.TypeLits as GHC


type family AlphaExprDim (t :: TE.EType) :: SP.Dim where
  AlphaExprDim TE.EReal = SP.D0
  AlphaExprDim TE.ECVec = SP.D1
  AlphaExprDim TE.ERVec = SP.D1
  AlphaExprDim TE.EMat = SP.D2
  AlphaExprDim TE.ESqMat = SP.D2
  AlphaExprDim (TE.EArray1 TE.EMat) = SP.D3
  AlphaExprDim q = GHC.TypeError (GHC.Text "Unsupported Type (" GHC.:<>: GHC.ShowType q GHC.:<>: GHC.Text ") in AlphaExprDim. Maybe add it?")

type family MapExprTypeToDim (ts :: [TE.EType]) :: [SP.Dim] where
  MapExprTypeToDim '[] = '[]
  MapExprTypeToDim (et ': ets) = AlphaExprDim et ': MapExprTypeToDim ets

addModelIndexes :: forall a b md gq .

                   SB.RowTypeTag a
                -> (a -> b)
                -> [DSum.DSum SB.GroupTypeTag (GroupFromData b)]
                -> SB.StanGroupBuilderM md gq ()
addModelIndexes rtt f gfds = traverse_ g gfds where
  g :: DSum.DSum SB.GroupTypeTag (GroupFromData b) -> SB.StanGroupBuilderM md gq ()
  g (gtt DSum.:=> gfd) = do
    let (GroupFromData _ mi _) = contraGroupFromData f gfd
    SB.addGroupIndexForData gtt rtt mi

addGroupIntMaps :: forall a b md gq .
                   SB.RowTypeTag a
                -> (a -> b)
                -> [DSum.DSum SB.GroupTypeTag (GroupFromData b)]
                -> SB.StanGroupBuilderM md gq ()
addGroupIntMaps rtt f gfds = traverse_ g gfds where
  g :: DSum.DSum SB.GroupTypeTag (GroupFromData b) -> SB.StanGroupBuilderM md gq ()
  g (gtt DSum.:=> gfd) = do
    let (GroupFromData _ _ gim) = contraGroupFromData f gfd
    SB.addGroupIntMapForDataSet gtt rtt gim

data AlphaByDataVecCW md gq where
  AlphaByDataVecCW :: (forall a . SB.RowTypeTag a -> SB.StanBuilderM md gq (TE.CodeWriter TE.VectorE)) -> AlphaByDataVecCW md gq

-- Do one time per model things: add parameters, etc.
setupAlpha :: forall md gq k t . GroupAlpha k t -> SB.StanBuilderM md gq (AlphaByDataVecCW md gq)
setupAlpha (GroupAlphaE bp avE _ _) = do
  aE <- DAG.parameterExpr <$> DAG.addBuildParameter bp
  let  f :: SB.RowTypeTag a -> SB.StanBuilderM md gq (TE.CodeWriter TE.VectorE)
       f rtt = pure $ pure $ avE aE rtt
  pure $ AlphaByDataVecCW f
setupAlpha (GroupAlphaCW bp avCW _ _) = do
  aE <- DAG.parameterExpr <$> DAG.addBuildParameter bp
  let f :: SB.RowTypeTag a -> SB.StanBuilderM md gq (TE.CodeWriter TE.VectorE)
      f rtt = pure $ avCW aE rtt
  pure $ AlphaByDataVecCW f
setupAlpha (GroupAlphaTD bp tdCW avCW _ _) = do
  aE <- DAG.parameterExpr <$> DAG.addBuildParameter bp
  let f :: SB.RowTypeTag a -> SB.StanBuilderM md gq (TE.CodeWriter TE.VectorE)
      f rtt = do
        let block = case SB.inputDataType rtt of
              SB.ModelData -> SB.SBTransformedData
              SB.GQData -> SB.SBTransformedDataGQ
        td <- SB.inBlock block $ SB.addFromCodeWriter $ tdCW rtt
        pure $ avCW td aE rtt
  pure $ AlphaByDataVecCW f
setupAlpha (GroupAlphaPrep bp prep avCW _ _) = do
  aE <- DAG.parameterExpr <$> DAG.addBuildParameter bp
  let f :: SB.RowTypeTag a -> SB.StanBuilderM md gq (TE.CodeWriter TE.VectorE)
      f rtt = do
        let block = case SB.inputDataType rtt of
              SB.ModelData -> SB.SBTransformedData
              SB.GQData -> SB.SBTransformedDataGQ
        a <- prep rtt
        pure $ avCW a aE rtt
  pure $ AlphaByDataVecCW f

tdAsPrep :: forall md gq td b . (forall a . SB.RowTypeTag a -> TE.CodeWriter td) -> SB.RowTypeTag b -> SB.StanBuilderM md gq td
tdAsPrep tdCW rtt = do
  let block = case SB.inputDataType rtt of
        SB.ModelData -> SB.SBTransformedData
        SB.GQData -> SB.SBTransformedDataGQ
  SB.inBlock block $ SB.addFromCodeWriter $ tdCW rtt

--newtype SomeGroupAlpha r = SomeGroupAlpha { someGroupAlpha :: forall t . GroupAlpha r t}

-- do once per data-set things and sum
setupAlphaSum' :: forall md gq r . NonEmpty (Some.Some (GroupAlpha r)) -> SB.StanBuilderM md gq (AlphaByDataVecCW md gq)
setupAlphaSum' gts = do
  abdvcws :: NonEmpty (AlphaByDataVecCW md gq) <- traverse (\x -> Some.withSome x setupAlpha)  gts
  let f :: SB.RowTypeTag a -> SB.StanBuilderM md gq (TE.CodeWriter TE.VectorE)
      f rtt = do
        x <- traverse (\abdv -> let (AlphaByDataVecCW g) = abdv in g rtt) abdvcws
        pure $ fmap (\z -> foldl' TE.plusE (head z) (tail z)) $ sequence x
  pure $ AlphaByDataVecCW f


setupAlphaSum :: forall md gq ts r . GroupAlphaList r ts -> SB.StanBuilderM md gq (AlphaByDataVecCW md gq)
setupAlphaSum gs  = maybe emptyErr setupAlphaSum' $ nonEmpty $ toSomeGroupAlphaList gs where
  toSomeGroupAlphaList :: GroupAlphaList r qs -> [Some.Some (GroupAlpha r)]
  toSomeGroupAlphaList TNil = []
  toSomeGroupAlphaList (g :> gs') = Some.mkSome g : toSomeGroupAlphaList gs'
  emptyErr = SB.stanBuildError "setupAlphaSum: empty GroupAlphaList given"


lookupAlphasPS :: forall r ts . GroupAlphaList r ts -> CS.StanSummary -> Either Text (PSList CS.StanStatistic (MapExprTypeToDim ts))
lookupAlphasPS TNil _ = Right PNil
lookupAlphasPS (ga :> gas) s = (:+) <$> lookupAlphaPS ga (CS.paramStats s) <*> lookupAlphasPS gas s

alphaPSToAlphaF :: GroupAlphaList k ts -> PSList CS.StanStatistic (MapExprTypeToDim ts) -> k -> Either Text [Double]
alphaPSToAlphaF TNil PNil _ = pure []
alphaPSToAlphaF (ga :> gas) (p :+ ps) k = (:) <$> indexAlphaPS ga p k <*> alphaPSToAlphaF gas ps k


data PSList :: Type -> [SP.Dim] -> Type where
  PNil :: PSList a '[]
  (:+) :: SP.ParameterStatistics d a -> PSList a ds -> PSList a (d ': ds)

type GroupAlphaList r = TypedList (GroupAlpha r)


--type FlippedPStatistics a d = SP.ParameterStatistics d a


data GroupFromData r k = GroupFromData { gfdGroup :: r -> k
                                       , gfdMakeIndex :: SB.MakeIndex r k
                                       , gfdMakeIntMap :: SB.DataToIntMap r k
                                       }

groupFromDataEnum :: (Show k, Enum k, Bounded k, Ord k) => (r -> k) -> GroupFromData r k
groupFromDataEnum f = GroupFromData f (SB.makeIndexFromEnum f) (SB.dataToIntMapFromEnum f)

contraGroupFromData :: (a -> b) -> GroupFromData b k -> GroupFromData a k
contraGroupFromData f (GroupFromData g mi di) = GroupFromData (g . f) (SB.contraMakeIndex f mi) (SB.contraDataToIntMap f di)

data GroupAlpha k t where
  GroupAlphaE :: DAG.BuildParameter t
              -> (forall a . TE.UExpr t -> SB.RowTypeTag a -> TE.VectorE)
              -> (Map String CS.StanStatistic -> Either Text (SP.ParameterStatistics (AlphaExprDim t) CS.StanStatistic))
              -> (k -> SP.ParameterStatistics (AlphaExprDim t) CS.StanStatistic -> Either Text Double)
             -> GroupAlpha k t
  GroupAlphaCW :: DAG.BuildParameter t
               -> (forall a . TE.UExpr t -> SB.RowTypeTag a -> TE.CodeWriter TE.VectorE)
               -> (Map String CS.StanStatistic -> Either Text (SP.ParameterStatistics (AlphaExprDim t) CS.StanStatistic))
               -> (k -> SP.ParameterStatistics (AlphaExprDim t) CS.StanStatistic -> Either Text Double)
               -> GroupAlpha k t
  GroupAlphaTD :: DAG.BuildParameter t
               -> (forall a . SB.RowTypeTag a -> TE.CodeWriter td)
               -> (forall a . td -> TE.UExpr t -> SB.RowTypeTag a -> TE.CodeWriter TE.VectorE)
               -> (Map String CS.StanStatistic -> Either Text (SP.ParameterStatistics (AlphaExprDim t) CS.StanStatistic))
               -> (k ->  SP.ParameterStatistics (AlphaExprDim t) CS.StanStatistic -> Either Text Double)
               -> GroupAlpha k t
  GroupAlphaPrep :: DAG.BuildParameter t
                 -> (forall a md gq . SB.RowTypeTag a -> SB.StanBuilderM md gq p)
                 -> (forall a . p -> TE.UExpr t -> SB.RowTypeTag a -> TE.CodeWriter TE.VectorE)
                 -> (Map String CS.StanStatistic -> Either Text (SP.ParameterStatistics (AlphaExprDim t) CS.StanStatistic))
                 -> (k -> SP.ParameterStatistics (AlphaExprDim t) CS.StanStatistic -> Either Text Double)
                 -> GroupAlpha k t

lookupAlphaPS :: GroupAlpha k t ->  Map String CS.StanStatistic -> Either Text (SP.ParameterStatistics (AlphaExprDim t) CS.StanStatistic)
lookupAlphaPS (GroupAlphaE _ _ lf _) = lf
lookupAlphaPS (GroupAlphaCW _ _ lf _) = lf
lookupAlphaPS (GroupAlphaTD _ _ _ lf _) = lf
lookupAlphaPS (GroupAlphaPrep _ _ _ lf _) = lf

indexAlphaPS :: GroupAlpha k t ->  SP.ParameterStatistics (AlphaExprDim t) CS.StanStatistic -> k -> Either Text Double
indexAlphaPS (GroupAlphaE _ _ _ pf) = flip pf
indexAlphaPS (GroupAlphaCW _ _ _ pf) = flip pf
indexAlphaPS (GroupAlphaTD _ _ _ _ pf) = flip pf
indexAlphaPS (GroupAlphaPrep _ _ _ _ pf) = flip pf

contramapGroupAlpha :: (q -> r) -> GroupAlpha r t -> GroupAlpha q t
contramapGroupAlpha h (GroupAlphaE bp vf lf rf) = GroupAlphaE bp vf lf (rf . h)
contramapGroupAlpha h (GroupAlphaCW bp cwvf lf rf) = GroupAlphaCW bp cwvf lf (rf . h)
contramapGroupAlpha h (GroupAlphaTD bp cwtd cwv lf rf) = GroupAlphaTD bp cwtd cwv lf (rf . h)
contramapGroupAlpha h (GroupAlphaPrep bp mp cwv lf rf) = GroupAlphaPrep bp mp cwv lf (rf . h)

{-
data Alpha k et where
  Alpha :: Alpha () TE.EReal
  GroupAlpha :: SB.GroupTypeTag k -> (k -> Either Text Int) -> Alpha k TE.ECVec
  GroupAlphaDC :: SB.GroupTypeTag k ->  (k -> Either Text Int) -> k -> Alpha k TE.ECVec
  BinaryAlpha :: SB.GroupTypeTag k -> (k -> Double) -> Alpha k TE.EReal
-}

zeroOrderAlpha :: DAG.BuildParameter TE.EReal -> GroupAlpha k TE.EReal
zeroOrderAlpha bp = GroupAlphaE bp f lf pf where
  f :: forall a . TE.RealE -> SB.RowTypeTag a -> TE.VectorE
  f aE _ = SF.scalarCVec aE
  lf =  SP.parseScalar (DAG.bParameterName bp)
  pf _ s =  Right $ SP.getScalar (fmap CS.mean s)

binarySI :: Maybe Text -> SB.GroupTypeTag k -> (k -> Double) -> (forall a . SB.RowTypeTag a -> TE.CodeWriter TE.VectorE)
binarySI prefixM gtt kScale = tdCW where
  indexVec :: SB.RowTypeTag a -> TE.VectorE
  indexVec rtt = TE.functionE SF.to_vector (SB.byGroupIndexE rtt gtt :> TNil)
  prefixed t = maybe t (<> "_" <> t) prefixM
  splitIndexNDS :: SB.RowTypeTag a -> TE.NamedDeclSpec TE.ECVec
  splitIndexNDS rtt = TE.NamedDeclSpec (prefixed "splitIndex_" <> SB.taggedGroupName gtt <> "_" <> SB.dataSetName rtt) $ TE.vectorSpec (SB.dataSetSizeE rtt) []
  tdCW :: SB.RowTypeTag a -> TE.CodeWriter TE.VectorE
  tdCW rtt = TE.declareRHSNW (splitIndexNDS rtt) $ TE.realE 2 `TE.timesE` (TE.realE 1.5 `TE.minusE` indexVec rtt)

binaryAlpha :: Maybe Text -> SB.GroupTypeTag k -> (k-> Double) -> DAG.BuildParameter TE.EReal -> GroupAlpha k TE.EReal
binaryAlpha prefixM gtt kScale bp = GroupAlphaTD bp tdCW f lf pf where
  tdCW :: forall a . SB.RowTypeTag a -> TE.CodeWriter TE.VectorE
  tdCW = binarySI prefixM gtt kScale
{-
  indexVec :: SB.RowTypeTag a -> TE.VectorE
  indexVec rtt = TE.functionE SF.to_vector (SB.byGroupIndexE rtt gtt :> TNil)
  prefixed t = maybe t (<> "_" <> t) prefixM
  splitIndexNDS :: SB.RowTypeTag a -> TE.NamedDeclSpec TE.ECVec
  splitIndexNDS rtt = TE.NamedDeclSpec (prefixed "splitIndex_" <> SB.taggedGroupName gtt <> "_" <> SB.dataSetName rtt) $ TE.vectorSpec (SB.dataSetSizeE rtt) []
  tdCW :: SB.RowTypeTag a -> TE.CodeWriter TE.VectorE
  tdCW rtt = TE.declareRHSNW (splitIndexNDS rtt) $ TE.realE 2 `TE.timesE` (TE.realE 1.5 `TE.minusE` indexVec rtt)
-}
  f :: TE.VectorE -> TE.UExpr TE.EReal -> SB.RowTypeTag a -> TE.CodeWriter TE.VectorE
  f splitIndex aE _rtt = pure $ aE `TE.timesE` splitIndex
  lf = SP.parseScalar (DAG.bParameterName bp)
  pf k s = Right $ kScale k * SP.getScalar (fmap CS.mean s)

safeIndexVector :: V.Vector a -> Int -> Either Text a
safeIndexVector v n = maybe (Left $ "safeIndexVector: bad index=" <> show n) Right $ v V.!? n

firstOrderAlpha :: SB.GroupTypeTag k -> (k -> Either Text Int) -> DAG.BuildParameter TE.ECVec -> GroupAlpha k TE.ECVec
firstOrderAlpha gtt index bp = GroupAlphaE bp f lf pf where
  f :: forall a . TE.VectorE -> SB.RowTypeTag a -> TE.VectorE
  f aE rtt = TE.indexE TE.s0 (SB.byGroupIndexE rtt gtt) aE
  lf = SP.parse1D (DAG.bParameterName bp)
  pf k s = index k >>= safeIndexVector (SP.getVector $ fmap CS.mean s)

-- dummy coding. For now just append 0. Would be helpful to choose where to put the zero so we could
-- choose which entry to dummy code.

dcPrep :: SB.GroupTypeTag k -> k -> SB.RowTypeTag a -> SB.StanBuilderM md gq (TE.Function TE.ECVec [TE.ECVec, TE.EInt], Int)
dcPrep gtt controlK rtt = do
  insert_zero_at <- vectorInsertZeroAtFunction
  (SB.IndexMap _ kgi _ _) <- SB.indexMap rtt gtt
  cn <- SB.stanBuildEither $ kgi controlK
  pure (insert_zero_at, cn)

firstOrderAlphaDC :: SB.GroupTypeTag k -> (k -> Either Text Int) -> k -> DAG.BuildParameter TE.ECVec -> GroupAlpha k TE.ECVec
firstOrderAlphaDC gtt index controlK bp = GroupAlphaPrep bp (dcPrep gtt controlK) f lf pf where
  f :: forall a . (TE.Function TE.ECVec [TE.ECVec, TE.EInt], Int) -> TE.VectorE -> SB.RowTypeTag a -> TE.CodeWriter TE.VectorE
  f (insert_zero_at, cn) aE rtt = do
    let aDCNDS = TE.NamedDeclSpec (DAG.bParameterName bp <> "_dc") $ TE.vectorSpec (SB.groupSizeE gtt) []
    aDC <- TE.declareRHSNW aDCNDS $ TE.functionE insert_zero_at (aE :> TE.intE cn :> TNil)
    pure $ TE.indexE TE.s0 (SB.byGroupIndexE rtt gtt) aDC
  lf = SP.parse1D (DAG.bParameterName bp)
  pf k s = do
    ik <- index k
    ic <- index controlK
    case compare ik ic of
      LT -> safeIndexVector (SP.getVector $ fmap CS.mean s) ik
      EQ -> pure 0
      GT -> safeIndexVector (SP.getVector $ fmap CS.mean s) (ik - 1)

secondOrderBinaryDC :: Maybe Text -> Maybe Text -> SB.GroupTypeTag bk -> (bk -> Double)
                    -> SB.GroupTypeTag dck -> (dck -> Either Text Int) -> dck
                    -> DAG.BuildParameter TE.ECVec
                    -> GroupAlpha (bk, dck) TE.ECVec
secondOrderBinaryDC prefixM siPrefixM bTag kScale dcTag index controlK bp = GroupAlphaPrep bp prep f lf pf where
  tdCW :: forall a . SB.RowTypeTag a -> TE.CodeWriter TE.VectorE
  tdCW = binarySI (siPrefixM <> prefixM) bTag kScale where
  prep ::  SB.RowTypeTag a -> SB.StanBuilderM md gq (TE.Function TE.ECVec [TE.ECVec, TE.EInt], Int, TE.VectorE)
  prep rtt = do
    (izf, index) <- dcPrep dcTag controlK rtt
    td <- tdAsPrep tdCW rtt
    pure $ (izf, index, td)
  f :: forall a . (TE.Function TE.ECVec [TE.ECVec, TE.EInt], Int, TE.VectorE) -> TE.VectorE -> SB.RowTypeTag a -> TE.CodeWriter TE.VectorE
  f (insertZeroAt, cn, siE) aE rtt = do
    let aDCNDS = TE.NamedDeclSpec (DAG.bParameterName bp <> "_dc") $ TE.vectorSpec (SB.groupSizeE dcTag) []
        eltTimes = TE.binaryOpE (TE.SElementWise TE.SMultiply)
    aDC <- TE.declareRHSNW aDCNDS $ TE.functionE insertZeroAt (aE :> TE.intE cn :> TNil)
    pure $ TE.indexE TE.s0 (SB.byGroupIndexE rtt dcTag) aDC `eltTimes` siE
  lf = SP.parse1D (DAG.bParameterName bp)
  pf (bk, dck) s = do
    ik <- index dck
    ic <- index controlK
    case compare ik ic of
      LT -> fmap (kScale bk *) $ safeIndexVector (SP.getVector $ fmap CS.mean s) ik
      EQ -> pure 0
      GT -> fmap (kScale bk *) $ safeIndexVector (SP.getVector $ fmap CS.mean s) (ik - 1)

vectorInsertZeroAtFunction :: SB.StanBuilderM md gq (TE.Function TE.ECVec [TE.ECVec, TE.EInt])
vectorInsertZeroAtFunction = do
  let le = TE.boolOpE TE.SLT
      eq = TE.boolOpE TE.SEq
      f :: TE.Function TE.ECVec [TE.ECVec, TE.EInt]
      f = TE.simpleFunction "vector_insert_zero_at"
  SB.addFunctionOnce f (TE.Arg "v" :> TE.Arg "n" :> TNil)
    $ \(v :> n :> TNil)  -> TE.writerL $ do
    szE <- TE.declareRHSNW (TE.NamedDeclSpec "m" $ TE.intSpec []) $ TE.functionE SF.size (v :> TNil) `TE.plusE` TE.intE 1
    wzero <- TE.declareNW (TE.NamedDeclSpec "wz" $ TE.vectorSpec szE [])
    TE.addStmt $ TE.for "l" (TE.SpecificNumbered (TE.intE 1) szE)
      $ \l -> [TE.ifThenElse
                ((l `le` n, (wzero `TE.at` l) `TE.assign` (v `TE.at` l)) :|
                [(l `eq` n, (wzero `TE.at` l) `TE.assign` TE.realE 0)])
                ((wzero `TE.at` l) `TE.assign` (v `TE.at` (l `TE.minusE` TE.intE 1)))]
    return wzero



secondOrderAlpha :: Maybe Text
                 -> SB.GroupTypeTag k1
                 -> (k1 -> Either Text Int)
                 -> SB.GroupTypeTag k2
                 -> (k2 -> Either Text Int)
                 -> DAG.BuildParameter TE.EMat
                 -> GroupAlpha (k1, k2) TE.EMat
secondOrderAlpha prefixM gtt1 index1 gtt2 index2 bp = GroupAlphaCW bp f lf pf where
  f :: forall a . TE.MatrixE -> SB.RowTypeTag a -> TE.CodeWriter TE.VectorE
  f aM rtt = do
    let index1 = SB.byGroupIndexE rtt gtt1
        index2 = SB.byGroupIndexE rtt gtt2
        prefixed t = maybe t (<> "_" <> t) prefixM
        alphaVNDS = TE.NamedDeclSpec (prefixed "aVec_" <> SB.taggedGroupName gtt1 <> "_" <> SB.taggedGroupName gtt2)
                 $ TE.vectorSpec (SB.dataSetSizeE rtt) []
        reIndexedAlpha = TE.indexE TE.s1 index2 $ TE.indexE TE.s0 index1 aM

    aV <- TE.declareNW alphaVNDS
    TE.addStmt
      $ TE.for "n" (TE.SpecificNumbered (TE.intE 1) $ SB.dataSetSizeE rtt)
      $ \nE -> [(aV `TE.at` nE) `TE.assign` TE.mAt reIndexedAlpha nE nE]
    pure aV
  lf = SP.parse2D (DAG.bParameterName bp)
  pf (k1, k2) s = do
    i1 <- index1 k1
    i2 <- index2 k2
    pure $ flip SP.getIndexed (i1, i2) $ fmap CS.mean s

thirdOrderAlpha :: Maybe Text
                -> SB.GroupTypeTag k1
                -> (k1 -> Either Text Int)
                -> SB.GroupTypeTag k2
                -> (k2 -> Either Text Int)
                -> SB.GroupTypeTag k3
                -> (k3 -> Either Text Int)
                -> DAG.BuildParameter (TE.EArray1 TE.EMat)
                -> GroupAlpha (k1, k2, k3) (TE.EArray1 TE.EMat)
thirdOrderAlpha prefixM gtt1 index1 gtt2 index2 gtt3 index3 bp = GroupAlphaCW bp f lf pf where
  f :: forall a . TE.ArrayE TE.EMat -> SB.RowTypeTag a -> TE.CodeWriter TE.VectorE
  f aM rtt = do
    let index1 = SB.byGroupIndexE rtt gtt1
        index2 = SB.byGroupIndexE rtt gtt2
        index3 = SB.byGroupIndexE rtt gtt3
        prefixed t = maybe t (<> "_" <> t) prefixM
        alphaVNDS = TE.NamedDeclSpec (prefixed "aVec_" <> SB.taggedGroupName gtt1 <> "_" <> SB.taggedGroupName gtt2 <> "_" <> SB.taggedGroupName gtt3)
                 $ TE.vectorSpec (SB.dataSetSizeE rtt) []
        reIndexedAlpha = TE.indexE TE.s2 (SB.byGroupIndexE rtt gtt3) $ TE.indexE TE.s1 (SB.byGroupIndexE rtt gtt2) $ TE.indexE TE.s0 (SB.byGroupIndexE rtt gtt1) aM

    aV <- TE.declareNW alphaVNDS
    TE.addStmt
      $ TE.for "n" (TE.SpecificNumbered (TE.intE 1) $ SB.dataSetSizeE rtt)
      $ \nE -> [(aV `TE.at` nE) `TE.assign` TE.mAt (reIndexedAlpha `TE.at` nE) nE nE]
    pure aV
  lf = SP.parse3D (DAG.bParameterName bp)
  pf (k1, k2, k3) s =  do
    i1 <- index1 k1
    i2 <- index2 k2
    i3 <- index3 k3
    pure $ flip SP.getIndexed (i1, i2, i3) $ fmap CS.mean s

secondOrderAlphaDC :: Maybe Text
                   -> SB.GroupTypeTag k1
                   -> (k1 -> Either Text Int, Int)
                   -> SB.GroupTypeTag k2
                   -> (k2 -> Either Text Int, Int)
                   -> (k1, k2)
                   -> DAG.BuildParameter TE.ECVec
                   -> GroupAlpha (k1, k2) TE.ECVec
secondOrderAlphaDC prefixM gtt1 (index1, sz1) gtt2 (index2 , sz2) (controlK1, controlK2) bp = GroupAlphaPrep bp prep f lf pf where
  prep :: SB.RowTypeTag a -> SB.StanBuilderM md gq (TE.Function TE.ECVec [TE.ECVec, TE.EInt], Int, Int)
  prep rtt = do
    insert_zero_at <- vectorInsertZeroAtFunction
    (SB.IndexMap _ kgi1 _ _) <- SB.indexMap rtt gtt1
    (SB.IndexMap _ kgi2 _ _) <- SB.indexMap rtt gtt2
    cn1 <- SB.stanBuildEither $ kgi1 controlK1
    cn2 <- SB.stanBuildEither $ kgi2 controlK2
    pure (insert_zero_at, cn1, cn2)

  f :: forall a . (TE.Function TE.ECVec [TE.ECVec, TE.EInt], Int, Int) -> TE.VectorE -> SB.RowTypeTag a -> TE.CodeWriter TE.VectorE
  f (insert_zero_at, cn1, cn2) aV rtt = do
    let gs1E = SB.groupSizeE gtt1
        gs2E = SB.groupSizeE gtt2
        neq = TE.boolOpE TE.SNEq
        or = TE.boolOpE TE.SOr
    let prefixed t = maybe t (<> "_" <> t) prefixM
        alphaMNDS = TE.NamedDeclSpec (prefixed "alpha_" <> SB.taggedGroupName gtt1 <> "_" <> SB.taggedGroupName gtt2)
                    $ TE.matrixSpec gs1E gs2E []
    am <- TE.declareNW alphaMNDS
    TE.addStmt $ TE.scoped $ TE.writerL' $ do
      let adcNDS = TE.NamedDeclSpec "withZero" $ TE.vectorSpec (gs1E `TE.timesE` gs2E) []
          czE = (TE.intE (cn1 - 1) `TE.timesE` gs2E) `TE.plusE` TE.intE cn2
      wzero <- TE.declareRHSNW adcNDS $ TE.functionE insert_zero_at (aV :> czE :> TNil)
      TE.addStmt $ TE.for "k1" (TE.SpecificNumbered (TE.intE 1) gs1E)
          $ \k1 -> [TE.for "k2" (TE.SpecificNumbered (TE.intE 1) gs2E)
               $ \k2 -> [TE.mAt am k1 k2
                        `TE.assign`
                        (TE.condE
                          ((k1 `neq` TE.intE cn1) `or` (k2 `neq` TE.intE cn2))
                          (wzero `TE.at` (((k1 `TE.minusE` TE.intE 1) `TE.timesE` gs2E) `TE.plusE` k2))
                          (TE.realE 0)
                        )]
               ]

    let index1 = SB.byGroupIndexE rtt gtt1
        index2 = SB.byGroupIndexE rtt gtt2
    SBB.vectorizeExpr (SB.dataSetSizeE rtt) (prefixed "alpha_" <> SB.taggedGroupName gtt1 <> "_" <> SB.taggedGroupName gtt2)
      $ \k -> TE.mAt (TE.indexE TE.s1 index2 (TE.indexE TE.s0 index1 am)) k k
  lf = SP.parse1D (DAG.bParameterName bp)
  pf (k1, k2) s = do
    i1 <- index1 k1
    i2 <- index2 k2
    c1i <- index1 controlK1
    c2i <- index2 controlK2
    let vi n1 n2 = (n1 - 1) * sz2 + n2
        i = vi i1 i2
        ci = vi c1i c2i
    case compare i ci of
      LT -> safeIndexVector (SP.getVector $ fmap CS.mean s) i
      EQ -> pure 0
      GT -> safeIndexVector (SP.getVector $ fmap CS.mean s) (i - 1)

thirdOrderAlphaDC :: SB.GroupTypeTag k1
                  -> (k1 -> Either Text Int, Int)
                  -> SB.GroupTypeTag k2
                  -> (k2 -> Either Text Int, Int)
                  -> SB.GroupTypeTag k3
                  -> (k3 -> Either Text Int, Int)
                  -> (k1, k2, k3)
                  -> DAG.BuildParameter TE.ECVec
                  -> GroupAlpha (k1, k2, k3) TE.ECVec
thirdOrderAlphaDC gtt1 (index1, sz1) gtt2 (index2, sz2) gtt3 (index3, sz3) (controlK1, controlK2, controlK3) bp = GroupAlphaPrep bp prep f lf pf where
  prep :: SB.RowTypeTag a -> SB.StanBuilderM md gq (TE.Function TE.ECVec [TE.ECVec, TE.EInt], Int, Int, Int)
  prep rtt = do
    insert_zero_at <- vectorInsertZeroAtFunction
    (SB.IndexMap _ kgi1 _ _) <- SB.indexMap rtt gtt1
    (SB.IndexMap _ kgi2 _ _) <- SB.indexMap rtt gtt2
    (SB.IndexMap _ kgi3 _ _) <- SB.indexMap rtt gtt3
    cn1 <- SB.stanBuildEither $ kgi1 controlK1
    cn2 <- SB.stanBuildEither $ kgi2 controlK2
    cn3 <- SB.stanBuildEither $ kgi3 controlK3
    pure (insert_zero_at, cn1, cn2, cn3)

  f :: forall a . (TE.Function TE.ECVec [TE.ECVec, TE.EInt], Int, Int, Int) -> TE.VectorE -> SB.RowTypeTag a -> TE.CodeWriter TE.VectorE
  f (insert_zero_at, cn1, cn2, cn3) aV rtt = do
    let gs1E = SB.groupSizeE gtt1
        gs2E = SB.groupSizeE gtt2
        gs3E = SB.groupSizeE gtt3
        neq = TE.boolOpE TE.SNEq
        or = TE.boolOpE TE.SOr
    let alphaMNDS = TE.NamedDeclSpec ("alpha_" <> SB.taggedGroupName gtt1 <> "_" <> SB.taggedGroupName gtt2 <> "_" <> SB.taggedGroupName gtt3)
                    $ TE.array1Spec gs1E (TE.matrixSpec gs2E gs3E [])
    am <- TE.declareNW alphaMNDS
    TE.addStmt $ TE.scoped $ TE.writerL' $ do
      let adcNDS = TE.NamedDeclSpec "withZero" $ TE.vectorSpec (gs1E `TE.timesE` gs2E `TE.timesE` gs3E) []
          czE = (TE.intE (cn1 - 1)  `TE.timesE` gs2E `TE.timesE` gs3E)
                `TE.plusE` (TE.intE (cn2 - 1) `TE.timesE` gs3E)
                `TE.plusE` TE.intE cn3
      wzero <- TE.declareRHSNW adcNDS $ TE.functionE insert_zero_at (aV :> czE :> TNil)
      TE.addStmt $ TE.for "k1" (TE.SpecificNumbered (TE.intE 1) gs1E)
          $ \k1 -> [TE.for "k2" (TE.SpecificNumbered (TE.intE 1) gs2E)
               $ \k2 -> [TE.for "k3" (TE.SpecificNumbered (TE.intE 1) gs3E)
                         $ \k3 -> [TE.mAt (am `TE.at` k1) k2 k3
                                   `TE.assign`
                                   (TE.condE
                                    ((k1 `neq` TE.intE cn1) `or` (k2 `neq` TE.intE cn2) `or` (k3 `neq` TE.intE cn3))
                                    (wzero `TE.at` ((k1 `TE.minusE` TE.intE 1) `TE.timesE` gs2E `TE.timesE` gs3E)
                                     `TE.plusE` ((k2 `TE.minusE` TE.intE 1) `TE.timesE` gs3E)
                                      `TE.plusE` k3)
                                    (TE.realE 0)
                                   )]
                        ]
               ]

    let index1 = SB.byGroupIndexE rtt gtt1
        index2 = SB.byGroupIndexE rtt gtt2
        index3 = SB.byGroupIndexE rtt gtt3
    SBB.vectorizeExpr (SB.dataSetSizeE rtt) ("alpha_" <> SB.taggedGroupName gtt1 <> "_" <> SB.taggedGroupName gtt2 <> "_" <> SB.taggedGroupName gtt3)
      $ \k -> TE.mAt (TE.slice0 k $ TE.indexE TE.s2 index3 (TE.indexE TE.s1 index2 (TE.indexE TE.s0 index1 am))) k k
  lf = SP.parse1D (DAG.bParameterName bp)
  pf (k1, k2, k3) s = do
    i1 <- index1 k1
    i2 <- index2 k2
    i3 <- index3 k3
    c1i <- index1 controlK1
    c2i <- index2 controlK2
    c3i <- index3 controlK3
    let vi n1 n2 n3 = (n1 - 1) * sz2 * sz3 + (n2 - 1) * sz3 + n3
        i = vi i1 i2 i3
        ci = vi c1i c2i c3i
    case compare i ci of
      LT -> safeIndexVector (SP.getVector $ fmap CS.mean s) i
      EQ -> pure 0
      GT -> safeIndexVector (SP.getVector $ fmap CS.mean s) i
--multipliers :: [Int] -> [Int]
--multipliers szs = scanr (\a b -> (a + 1) * b) 1 $ List.tail szs


{-
newtype Control k = Control k
newtype Controls = Controls (DHash.DHashMap SB.GroupTypeTag Control)

numCategoriesE :: Controls -> TE.IntE
numCategoriesE (Controls controls) =
  case nonEmpty (DHash.toList controls) of
    Nothing -> TE.intE 0
    Just ((hGtt DSum.:=> _) :| tail) ->
      DHash.foldlWithKey (\nE gtt _ -> nE `TE.timesE` SB.groupSizeE gtt) (SB.groupSizeE hGtt) (DHash.fromList tail)


vectorIndexFromMatrixIndex :: [(Int, Int)] -> Int
vectorIndexFromMatrixIndex sis =
  let (sizes, indexes) = unzip sis
  in foldl' (+) 0 $ zipWith (*) (multipliers sizes) indexes

data SizeAndIndex k = SizeAndIndex Int Int

sizesAndIndexes :: SB.RowTypeTag a -> Controls -> SB.StanBuilderM md gq ([Int], [Int])
sizesAndIndexes rtt (Controls controls) = do
  let sizeAndIndex :: SB.GroupTypeTag k -> Control k -> SB.StanBuilderM md gq (SizeAndIndex k)
      sizeAndIndex gtt (Control k) = do
        (SB.IndexMap _ kgi gigk _) <- SB.indexMap rtt gtt
        let size = IntMap.size gigk
        index <- SB.stanBuildEither $ kgi k
        pure $ SizeAndIndex size index
  sizesAndIndexes <- DHash.traverseWithKey sizeAndIndex controls
  pure $ unzip $ fmap (\(DHash.Some (SizeAndIndex s i)) -> (s, i)) $ DHash.elems sizesAndIndexes

controlIndex :: SB.RowTypeTag a -> Controls -> SB.StanBuilderM md gq Int
controlIndex rtt c@(Controls controls) = do
  (sizes, indexes) <- sizesAndIndexes rtt c
  pure $ foldl' (+) 0 $ zipWith (*) sizes indexes

multiDimFromVec :: forall t md gq .
                  => Controls -> TE.VectorE -> TE.NamedDeclSpec t -> TE.CodeWriter (TE.UExpr t)
multiDimFromVec (Controls controls) v nds =
  case DHash.size controls of
    1 -> case nds of
      TE.NamedDeclSpec _ (TE.DeclSpec TE.StanVector _ _) -> TE.declareRHSNW nds v
      -> multiDimFromVec' controls v nds
    _ -> multiDimFromVec' controls v nds

multiDimFromVec' :: forall t md gq .
                 =>  Controls -> TE.VectorE -> TE.NamedDeclSpec t -> TE.CodeWriter (TE.UExpr t)
multiDimFromVec' controls v nds = do
  let sizeEs = fmap (\(DHash.Some gtt) -> SB.groupSizeE gtt) $ DHash.keys controls
      withVec :: TE.NamedDeclSpec t -> Vec.Vec n TE.EInt -> TE.CodeWriter (TE.UExpr t)
      vecSizesM :: Maybe (Vec.Vec (Dimension t) TE.IntE)= Vec.fromList sizeEs
  md <- TE.declareNW nds
  TE.addStmt $ TE.intVecLoops
-}





{-
matrixInsertZeroAtFunction :: SB.StanBuilderM md gq (TE.Function TE.EMat [TE.EMat, TE.EInt, TE.EInt])
matrixInsertZeroAtFunction = do
  let le = TE.boolOpE TE.SLT
      eq = TE.boolOpE TE.SEq
      f :: TE.Function TE.EMat [TE.EMat, TE.EInt, TE.EInt]
      f = TE.simpleFunction "matrix_insert_zero_at"
  SB.addFunctionOnce f (TE.Arg "m" :> TE.Arg "n" :> TE.Arg "m" :> TNil)
    $ \(m :> n :> m :> TNil)  -> TE.writerL $ do
    szE <- TE.declareRHSNW (TE.NamedDeclSpec "m" $ TE.intSpec []) $ TE.functionE SF.size (v :> TNil) `TE.plusE` TE.intE 1
    wzero <- TE.declareNW (TE.NamedDeclSpec "wz" $ TE.vectorSpec szE [])
--             $ TE.functionE SF.rep_vector (TE.realE 0 :> szE :> TNil)
    TE.addStmt $ TE.for "l" (TE.SpecificNumbered (TE.intE 1) szE)
      $ \l -> [TE.ifThenElse
                ((l `le` n, (wzero `TE.at` l) `TE.assign` (v `TE.at` l)) :|
                [(l `eq` n, (wzero `TE.at` l) `TE.assign` TE.realE 0)])
                ((wzero `TE.at` l) `TE.assign` (v `TE.at` (l `TE.minusE` TE.intE 1)))]
    return wzero
-}
