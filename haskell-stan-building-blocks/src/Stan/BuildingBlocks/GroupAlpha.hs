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
module Stan.BuildingBlocks.GroupAlpha
  (
    module Stan.BuildingBlocks.GroupAlpha
  )
where

import Prelude hiding (sum, All)

import qualified Stan.Language as SL
import qualified Stan.Language.Statement as SL
import Stan.Language (TypedList(..))
import Stan.Language.Recursion (hfmap)
import qualified Stan.Functions as SF
import Stan.Functions.Operators
import qualified Stan.Builder as SB
import qualified Stan.BuildingBlocks.ArrayHelpers as SBBA
import qualified Stan.BuildingBlocks.Distributions as SBD

--import qualified CmdStan.Types as CS

import qualified Data.List as List
import qualified Data.Dependent.Sum as DSum
import qualified Data.Some as Some
import qualified Data.Dependent.HashMap as DHash
import qualified Data.IntMap as IntMap
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as VU

import qualified Data.Vec.Lazy as Vec
import qualified Data.Type.Nat as DT

import qualified GHC.TypeLits as GHC


type family AlphaExprDim (t :: SL.EType) :: SP.Dim where
  AlphaExprDim SL.EReal = SP.D0
  AlphaExprDim SL.ECVec = SP.D1
  AlphaExprDim SL.ERVec = SP.D1
  AlphaExprDim SL.EMat = SP.D2
  AlphaExprDim SL.ESqMat = SP.D2
  AlphaExprDim (SL.EArray1 SL.EMat) = SP.D3
  AlphaExprDim q = GHC.TypeError (GHC.Text "Unsupported Type (" GHC.:<>: GHC.ShowType q GHC.:<>: GHC.Text ") in AlphaExprDim. Maybe add it?")

type family MapExprTypeToDim (ts :: [SL.EType]) :: [SP.Dim] where
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
  AlphaByDataVecCW :: (forall a . SB.RowTypeTag a -> SB.StanBuilderM md gq (SL.CodeWriter SL.VectorE)) -> AlphaByDataVecCW md gq

-- Do one time per model things: add parameters, etc.
setupAlpha :: forall md gq k t . GroupAlpha k t -> SB.StanBuilderM md gq (AlphaByDataVecCW md gq)
setupAlpha (GroupAlphaE bp avE _ _) = do
  aE <- DAG.parameterExpr <$> DAG.addBuildParameter bp
  let  f :: SB.RowTypeTag a -> SB.StanBuilderM md gq (SL.CodeWriter SL.VectorE)
       f rtt = pure $ pure $ avE aE rtt
  pure $ AlphaByDataVecCW f
setupAlpha (GroupAlphaCW bp avCW _ _) = do
  aE <- DAG.parameterExpr <$> DAG.addBuildParameter bp
  let f :: SB.RowTypeTag a -> SB.StanBuilderM md gq (SL.CodeWriter SL.VectorE)
      f rtt = pure $ avCW aE rtt
  pure $ AlphaByDataVecCW f
setupAlpha (GroupAlphaTD bp tdCW avCW _ _) = do
  aE <- DAG.parameterExpr <$> DAG.addBuildParameter bp
  let f :: SB.RowTypeTag a -> SB.StanBuilderM md gq (SL.CodeWriter SL.VectorE)
      f rtt = do
        let block = case SB.inputDataType rtt of
              SB.ModelData -> SB.SBTransformedData
              SB.GQData -> SB.SBTransformedDataGQ
        td <- SB.inBlock block $ SB.addFromCodeWriter $ tdCW rtt
        pure $ avCW td aE rtt
  pure $ AlphaByDataVecCW f
setupAlpha (GroupAlphaPrep bp prep avCW _ _) = do
  aE <- DAG.parameterExpr <$> DAG.addBuildParameter bp
  let f :: SB.RowTypeTag a -> SB.StanBuilderM md gq (SL.CodeWriter SL.VectorE)
      f rtt = do
        let block = case SB.inputDataType rtt of
              SB.ModelData -> SB.SBTransformedData
              SB.GQData -> SB.SBTransformedDataGQ
        a <- prep rtt
        pure $ avCW a aE rtt
  pure $ AlphaByDataVecCW f

tdAsPrep :: forall md gq td b . (forall a . SB.RowTypeTag a -> SL.CodeWriter td) -> SB.RowTypeTag b -> SB.StanBuilderM md gq td
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
  let f :: SB.RowTypeTag a -> SB.StanBuilderM md gq (SL.CodeWriter SL.VectorE)
      f rtt = do
        x <- traverse (\abdv -> let (AlphaByDataVecCW g) = abdv in g rtt) abdvcws
        pure $ fmap (\z -> foldl' SL.plusE (head z) (tail z)) $ sequence x
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
              -> (forall a . SL.UExpr t -> SB.RowTypeTag a -> SL.VectorE)
              -> (Map String CS.StanStatistic -> Either Text (SP.ParameterStatistics (AlphaExprDim t) CS.StanStatistic))
              -> (k -> SP.ParameterStatistics (AlphaExprDim t) CS.StanStatistic -> Either Text Double)
             -> GroupAlpha k t
  GroupAlphaCW :: DAG.BuildParameter t
               -> (forall a . SL.UExpr t -> SB.RowTypeTag a -> SL.CodeWriter SL.VectorE)
               -> (Map String CS.StanStatistic -> Either Text (SP.ParameterStatistics (AlphaExprDim t) CS.StanStatistic))
               -> (k -> SP.ParameterStatistics (AlphaExprDim t) CS.StanStatistic -> Either Text Double)
               -> GroupAlpha k t
  GroupAlphaTD :: DAG.BuildParameter t
               -> (forall a . SB.RowTypeTag a -> SL.CodeWriter td)
               -> (forall a . td -> SL.UExpr t -> SB.RowTypeTag a -> SL.CodeWriter SL.VectorE)
               -> (Map String CS.StanStatistic -> Either Text (SP.ParameterStatistics (AlphaExprDim t) CS.StanStatistic))
               -> (k ->  SP.ParameterStatistics (AlphaExprDim t) CS.StanStatistic -> Either Text Double)
               -> GroupAlpha k t
  GroupAlphaPrep :: DAG.BuildParameter t
                 -> (forall a md gq . SB.RowTypeTag a -> SB.StanBuilderM md gq p)
                 -> (forall a . p -> SL.UExpr t -> SB.RowTypeTag a -> SL.CodeWriter SL.VectorE)
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
  Alpha :: Alpha () SL.EReal
  GroupAlpha :: SB.GroupTypeTag k -> (k -> Either Text Int) -> Alpha k SL.ECVec
  GroupAlphaDC :: SB.GroupTypeTag k ->  (k -> Either Text Int) -> k -> Alpha k SL.ECVec
  BinaryAlpha :: SB.GroupTypeTag k -> (k -> Double) -> Alpha k SL.EReal
-}

zeroOrderAlpha :: DAG.BuildParameter SL.EReal -> GroupAlpha k SL.EReal
zeroOrderAlpha bp = GroupAlphaE bp f lf pf where
  f :: forall a . SL.RealE -> SB.RowTypeTag a -> SL.VectorE
  f aE _ = SF.scalarCVec aE
  lf =  SP.parseScalar (DAG.bParameterName bp)
  pf _ s =  Right $ SP.getScalar (fmap CS.mean s)

binarySI :: Maybe Text -> SB.GroupTypeTag k -> (k -> Double) -> (forall a . SB.RowTypeTag a -> SL.CodeWriter SL.VectorE)
binarySI prefixM gtt kScale = tdCW where
  indexVec :: SB.RowTypeTag a -> SL.VectorE
  indexVec rtt = SL.functionE SF.to_vector (SB.byGroupIndexE rtt gtt :> TNil)
  prefixed t = maybe t (<> "_" <> t) prefixM
  splitIndexNDS :: SB.RowTypeTag a -> SL.NamedDeclSpec SL.ECVec
  splitIndexNDS rtt = SL.NamedDeclSpec (prefixed "splitIndex_" <> SB.taggedGroupName gtt <> "_" <> SB.dataSetName rtt) $ SL.vectorSpec (SB.dataSetSizeE rtt) []
  tdCW :: SB.RowTypeTag a -> SL.CodeWriter SL.VectorE
  tdCW rtt = SL.declareRHSNW (splitIndexNDS rtt) $ SL.realE 2 `SL.timesE` (SL.realE 1.5 `SL.minusE` indexVec rtt)

binaryAlpha :: Maybe Text -> SB.GroupTypeTag k -> (k-> Double) -> DAG.BuildParameter SL.EReal -> GroupAlpha k SL.EReal
binaryAlpha prefixM gtt kScale bp = GroupAlphaTD bp tdCW f lf pf where
  tdCW :: forall a . SB.RowTypeTag a -> SL.CodeWriter SL.VectorE
  tdCW = binarySI prefixM gtt kScale
{-
  indexVec :: SB.RowTypeTag a -> SL.VectorE
  indexVec rtt = SL.functionE SF.to_vector (SB.byGroupIndexE rtt gtt :> TNil)
  prefixed t = maybe t (<> "_" <> t) prefixM
  splitIndexNDS :: SB.RowTypeTag a -> SL.NamedDeclSpec SL.ECVec
  splitIndexNDS rtt = SL.NamedDeclSpec (prefixed "splitIndex_" <> SB.taggedGroupName gtt <> "_" <> SB.dataSetName rtt) $ SL.vectorSpec (SB.dataSetSizeE rtt) []
  tdCW :: SB.RowTypeTag a -> SL.CodeWriter SL.VectorE
  tdCW rtt = SL.declareRHSNW (splitIndexNDS rtt) $ SL.realE 2 `SL.timesE` (SL.realE 1.5 `SL.minusE` indexVec rtt)
-}
  f :: SL.VectorE -> SL.UExpr SL.EReal -> SB.RowTypeTag a -> SL.CodeWriter SL.VectorE
  f splitIndex aE _rtt = pure $ aE `SL.timesE` splitIndex
  lf = SP.parseScalar (DAG.bParameterName bp)
  pf k s = Right $ kScale k * SP.getScalar (fmap CS.mean s)

safeIndexVector :: V.Vector a -> Int -> Either Text a
safeIndexVector v n = maybe (Left $ "safeIndexVector: bad index=" <> show n) Right $ v V.!? n

firstOrderAlpha :: SB.GroupTypeTag k -> (k -> Either Text Int) -> DAG.BuildParameter SL.ECVec -> GroupAlpha k SL.ECVec
firstOrderAlpha gtt index bp = GroupAlphaE bp f lf pf where
  f :: forall a . SL.VectorE -> SB.RowTypeTag a -> SL.VectorE
  f aE rtt = SL.indexE SL.s0 (SB.byGroupIndexE rtt gtt) aE
  lf = SP.parse1D (DAG.bParameterName bp)
  pf k s = index k >>= safeIndexVector (SP.getVector $ fmap CS.mean s)

-- dummy coding. For now just append 0. Would be helpful to choose where to put the zero so we could
-- choose which entry to dummy code.

dcPrep :: SB.GroupTypeTag k -> k -> SB.RowTypeTag a -> SB.StanBuilderM md gq (SL.Function SL.ECVec [SL.ECVec, SL.EInt], Int)
dcPrep gtt controlK rtt = do
  insert_zero_at <- vectorInsertZeroAtFunction
  (SB.IndexMap _ kgi _ _) <- SB.indexMap rtt gtt
  cn <- SB.stanBuildEither $ kgi controlK
  pure (insert_zero_at, cn)

firstOrderAlphaDC :: SB.GroupTypeTag k -> (k -> Either Text Int) -> k -> DAG.BuildParameter SL.ECVec -> GroupAlpha k SL.ECVec
firstOrderAlphaDC gtt index controlK bp = GroupAlphaPrep bp (dcPrep gtt controlK) f lf pf where
  f :: forall a . (SL.Function SL.ECVec [SL.ECVec, SL.EInt], Int) -> SL.VectorE -> SB.RowTypeTag a -> SL.CodeWriter SL.VectorE
  f (insert_zero_at, cn) aE rtt = do
    let aDCNDS = SL.NamedDeclSpec (DAG.bParameterName bp <> "_dc") $ SL.vectorSpec (SB.groupSizeE gtt) []
    aDC <- SL.declareRHSNW aDCNDS $ SL.functionE insert_zero_at (aE :> SL.intE cn :> TNil)
    pure $ SL.indexE SL.s0 (SB.byGroupIndexE rtt gtt) aDC
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
                    -> DAG.BuildParameter SL.ECVec
                    -> GroupAlpha (bk, dck) SL.ECVec
secondOrderBinaryDC prefixM siPrefixM bTag kScale dcTag index controlK bp = GroupAlphaPrep bp prep f lf pf where
  tdCW :: forall a . SB.RowTypeTag a -> SL.CodeWriter SL.VectorE
  tdCW = binarySI (siPrefixM <> prefixM) bTag kScale where
  prep ::  SB.RowTypeTag a -> SB.StanBuilderM md gq (SL.Function SL.ECVec [SL.ECVec, SL.EInt], Int, SL.VectorE)
  prep rtt = do
    (izf, index) <- dcPrep dcTag controlK rtt
    td <- tdAsPrep tdCW rtt
    pure $ (izf, index, td)
  f :: forall a . (SL.Function SL.ECVec [SL.ECVec, SL.EInt], Int, SL.VectorE) -> SL.VectorE -> SB.RowTypeTag a -> SL.CodeWriter SL.VectorE
  f (insertZeroAt, cn, siE) aE rtt = do
    let aDCNDS = SL.NamedDeclSpec (DAG.bParameterName bp <> "_dc") $ SL.vectorSpec (SB.groupSizeE dcTag) []
        eltTimes = SL.binaryOpE (SL.SElementWise SL.SMultiply)
    aDC <- SL.declareRHSNW aDCNDS $ SL.functionE insertZeroAt (aE :> SL.intE cn :> TNil)
    pure $ SL.indexE SL.s0 (SB.byGroupIndexE rtt dcTag) aDC `eltTimes` siE
  lf = SP.parse1D (DAG.bParameterName bp)
  pf (bk, dck) s = do
    ik <- index dck
    ic <- index controlK
    case compare ik ic of
      LT -> fmap (kScale bk *) $ safeIndexVector (SP.getVector $ fmap CS.mean s) ik
      EQ -> pure 0
      GT -> fmap (kScale bk *) $ safeIndexVector (SP.getVector $ fmap CS.mean s) (ik - 1)

vectorInsertZeroAtFunction :: SB.StanBuilderM md gq (SL.Function SL.ECVec [SL.ECVec, SL.EInt])
vectorInsertZeroAtFunction = do
  let le = SL.boolOpE SL.SLT
      eq = SL.boolOpE SL.SEq
      f :: SL.Function SL.ECVec [SL.ECVec, SL.EInt]
      f = SL.simpleFunction "vector_insert_zero_at"
  SB.addFunctionOnce f (SL.Arg "v" :> SL.Arg "n" :> TNil)
    $ \(v :> n :> TNil)  -> SL.writerL $ do
    szE <- SL.declareRHSNW (SL.NamedDeclSpec "m" $ SL.intSpec []) $ SL.functionE SF.size (v :> TNil) `SL.plusE` SL.intE 1
    wzero <- SL.declareNW (SL.NamedDeclSpec "wz" $ SL.vectorSpec szE [])
    SL.addStmt $ SL.for "l" (SL.SpecificNumbered (SL.intE 1) szE)
      $ \l -> [SL.ifThenElse
                ((l `le` n, (wzero `SL.at` l) `SL.assign` (v `SL.at` l)) :|
                [(l `eq` n, (wzero `SL.at` l) `SL.assign` SL.realE 0)])
                ((wzero `SL.at` l) `SL.assign` (v `SL.at` (l `SL.minusE` SL.intE 1)))]
    return wzero



secondOrderAlpha :: Maybe Text
                 -> SB.GroupTypeTag k1
                 -> (k1 -> Either Text Int)
                 -> SB.GroupTypeTag k2
                 -> (k2 -> Either Text Int)
                 -> DAG.BuildParameter SL.EMat
                 -> GroupAlpha (k1, k2) SL.EMat
secondOrderAlpha prefixM gtt1 index1 gtt2 index2 bp = GroupAlphaCW bp f lf pf where
  f :: forall a . SL.MatrixE -> SB.RowTypeTag a -> SL.CodeWriter SL.VectorE
  f aM rtt = do
    let index1 = SB.byGroupIndexE rtt gtt1
        index2 = SB.byGroupIndexE rtt gtt2
        prefixed t = maybe t (<> "_" <> t) prefixM
        alphaVNDS = SL.NamedDeclSpec (prefixed "aVec_" <> SB.taggedGroupName gtt1 <> "_" <> SB.taggedGroupName gtt2)
                 $ SL.vectorSpec (SB.dataSetSizeE rtt) []
        reIndexedAlpha = SL.indexE SL.s1 index2 $ SL.indexE SL.s0 index1 aM

    aV <- SL.declareNW alphaVNDS
    SL.addStmt
      $ SL.for "n" (SL.SpecificNumbered (SL.intE 1) $ SB.dataSetSizeE rtt)
      $ \nE -> [(aV `SL.at` nE) `SL.assign` SL.mAt reIndexedAlpha nE nE]
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
                -> DAG.BuildParameter (SL.EArray1 SL.EMat)
                -> GroupAlpha (k1, k2, k3) (SL.EArray1 SL.EMat)
thirdOrderAlpha prefixM gtt1 index1 gtt2 index2 gtt3 index3 bp = GroupAlphaCW bp f lf pf where
  f :: forall a . SL.ArrayE SL.EMat -> SB.RowTypeTag a -> SL.CodeWriter SL.VectorE
  f aM rtt = do
    let index1 = SB.byGroupIndexE rtt gtt1
        index2 = SB.byGroupIndexE rtt gtt2
        index3 = SB.byGroupIndexE rtt gtt3
        prefixed t = maybe t (<> "_" <> t) prefixM
        alphaVNDS = SL.NamedDeclSpec (prefixed "aVec_" <> SB.taggedGroupName gtt1 <> "_" <> SB.taggedGroupName gtt2 <> "_" <> SB.taggedGroupName gtt3)
                 $ SL.vectorSpec (SB.dataSetSizeE rtt) []
        reIndexedAlpha = SL.indexE SL.s2 (SB.byGroupIndexE rtt gtt3) $ SL.indexE SL.s1 (SB.byGroupIndexE rtt gtt2) $ SL.indexE SL.s0 (SB.byGroupIndexE rtt gtt1) aM

    aV <- SL.declareNW alphaVNDS
    SL.addStmt
      $ SL.for "n" (SL.SpecificNumbered (SL.intE 1) $ SB.dataSetSizeE rtt)
      $ \nE -> [(aV `SL.at` nE) `SL.assign` SL.mAt (reIndexedAlpha `SL.at` nE) nE nE]
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
                   -> DAG.BuildParameter SL.ECVec
                   -> GroupAlpha (k1, k2) SL.ECVec
secondOrderAlphaDC prefixM gtt1 (index1, sz1) gtt2 (index2 , sz2) (controlK1, controlK2) bp = GroupAlphaPrep bp prep f lf pf where
  prep :: SB.RowTypeTag a -> SB.StanBuilderM md gq (SL.Function SL.ECVec [SL.ECVec, SL.EInt], Int, Int)
  prep rtt = do
    insert_zero_at <- vectorInsertZeroAtFunction
    (SB.IndexMap _ kgi1 _ _) <- SB.indexMap rtt gtt1
    (SB.IndexMap _ kgi2 _ _) <- SB.indexMap rtt gtt2
    cn1 <- SB.stanBuildEither $ kgi1 controlK1
    cn2 <- SB.stanBuildEither $ kgi2 controlK2
    pure (insert_zero_at, cn1, cn2)

  f :: forall a . (SL.Function SL.ECVec [SL.ECVec, SL.EInt], Int, Int) -> SL.VectorE -> SB.RowTypeTag a -> SL.CodeWriter SL.VectorE
  f (insert_zero_at, cn1, cn2) aV rtt = do
    let gs1E = SB.groupSizeE gtt1
        gs2E = SB.groupSizeE gtt2
        neq = SL.boolOpE SL.SNEq
        or = SL.boolOpE SL.SOr
    let prefixed t = maybe t (<> "_" <> t) prefixM
        alphaMNDS = SL.NamedDeclSpec (prefixed "alpha_" <> SB.taggedGroupName gtt1 <> "_" <> SB.taggedGroupName gtt2)
                    $ SL.matrixSpec gs1E gs2E []
    am <- SL.declareNW alphaMNDS
    SL.addStmt $ SL.scoped $ SL.writerL' $ do
      let adcNDS = SL.NamedDeclSpec "withZero" $ SL.vectorSpec (gs1E `SL.timesE` gs2E) []
          czE = (SL.intE (cn1 - 1) `SL.timesE` gs2E) `SL.plusE` SL.intE cn2
      wzero <- SL.declareRHSNW adcNDS $ SL.functionE insert_zero_at (aV :> czE :> TNil)
      SL.addStmt $ SL.for "k1" (SL.SpecificNumbered (SL.intE 1) gs1E)
          $ \k1 -> [SL.for "k2" (SL.SpecificNumbered (SL.intE 1) gs2E)
               $ \k2 -> [SL.mAt am k1 k2
                        `SL.assign`
                        (SL.condE
                          ((k1 `neq` SL.intE cn1) `or` (k2 `neq` SL.intE cn2))
                          (wzero `SL.at` (((k1 `SL.minusE` SL.intE 1) `SL.timesE` gs2E) `SL.plusE` k2))
                          (SL.realE 0)
                        )]
               ]

    let index1 = SB.byGroupIndexE rtt gtt1
        index2 = SB.byGroupIndexE rtt gtt2
    SBB.vectorizeExpr (SB.dataSetSizeE rtt) (prefixed "alpha_" <> SB.taggedGroupName gtt1 <> "_" <> SB.taggedGroupName gtt2)
      $ \k -> SL.mAt (SL.indexE SL.s1 index2 (SL.indexE SL.s0 index1 am)) k k
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
                  -> DAG.BuildParameter SL.ECVec
                  -> GroupAlpha (k1, k2, k3) SL.ECVec
thirdOrderAlphaDC gtt1 (index1, sz1) gtt2 (index2, sz2) gtt3 (index3, sz3) (controlK1, controlK2, controlK3) bp = GroupAlphaPrep bp prep f lf pf where
  prep :: SB.RowTypeTag a -> SB.StanBuilderM md gq (SL.Function SL.ECVec [SL.ECVec, SL.EInt], Int, Int, Int)
  prep rtt = do
    insert_zero_at <- vectorInsertZeroAtFunction
    (SB.IndexMap _ kgi1 _ _) <- SB.indexMap rtt gtt1
    (SB.IndexMap _ kgi2 _ _) <- SB.indexMap rtt gtt2
    (SB.IndexMap _ kgi3 _ _) <- SB.indexMap rtt gtt3
    cn1 <- SB.stanBuildEither $ kgi1 controlK1
    cn2 <- SB.stanBuildEither $ kgi2 controlK2
    cn3 <- SB.stanBuildEither $ kgi3 controlK3
    pure (insert_zero_at, cn1, cn2, cn3)

  f :: forall a . (SL.Function SL.ECVec [SL.ECVec, SL.EInt], Int, Int, Int) -> SL.VectorE -> SB.RowTypeTag a -> SL.CodeWriter SL.VectorE
  f (insert_zero_at, cn1, cn2, cn3) aV rtt = do
    let gs1E = SB.groupSizeE gtt1
        gs2E = SB.groupSizeE gtt2
        gs3E = SB.groupSizeE gtt3
        neq = SL.boolOpE SL.SNEq
        or = SL.boolOpE SL.SOr
    let alphaMNDS = SL.NamedDeclSpec ("alpha_" <> SB.taggedGroupName gtt1 <> "_" <> SB.taggedGroupName gtt2 <> "_" <> SB.taggedGroupName gtt3)
                    $ SL.array1Spec gs1E (SL.matrixSpec gs2E gs3E [])
    am <- SL.declareNW alphaMNDS
    SL.addStmt $ SL.scoped $ SL.writerL' $ do
      let adcNDS = SL.NamedDeclSpec "withZero" $ SL.vectorSpec (gs1E `SL.timesE` gs2E `SL.timesE` gs3E) []
          czE = (SL.intE (cn1 - 1)  `SL.timesE` gs2E `SL.timesE` gs3E)
                `SL.plusE` (SL.intE (cn2 - 1) `SL.timesE` gs3E)
                `SL.plusE` SL.intE cn3
      wzero <- SL.declareRHSNW adcNDS $ SL.functionE insert_zero_at (aV :> czE :> TNil)
      SL.addStmt $ SL.for "k1" (SL.SpecificNumbered (SL.intE 1) gs1E)
          $ \k1 -> [SL.for "k2" (SL.SpecificNumbered (SL.intE 1) gs2E)
               $ \k2 -> [SL.for "k3" (SL.SpecificNumbered (SL.intE 1) gs3E)
                         $ \k3 -> [SL.mAt (am `SL.at` k1) k2 k3
                                   `SL.assign`
                                   (SL.condE
                                    ((k1 `neq` SL.intE cn1) `or` (k2 `neq` SL.intE cn2) `or` (k3 `neq` SL.intE cn3))
                                    (wzero `SL.at` ((k1 `SL.minusE` SL.intE 1) `SL.timesE` gs2E `SL.timesE` gs3E)
                                     `SL.plusE` ((k2 `SL.minusE` SL.intE 1) `SL.timesE` gs3E)
                                      `SL.plusE` k3)
                                    (SL.realE 0)
                                   )]
                        ]
               ]

    let index1 = SB.byGroupIndexE rtt gtt1
        index2 = SB.byGroupIndexE rtt gtt2
        index3 = SB.byGroupIndexE rtt gtt3
    SBB.vectorizeExpr (SB.dataSetSizeE rtt) ("alpha_" <> SB.taggedGroupName gtt1 <> "_" <> SB.taggedGroupName gtt2 <> "_" <> SB.taggedGroupName gtt3)
      $ \k -> SL.mAt (SL.slice0 k $ SL.indexE SL.s2 index3 (SL.indexE SL.s1 index2 (SL.indexE SL.s0 index1 am))) k k
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

numCategoriesE :: Controls -> SL.IntE
numCategoriesE (Controls controls) =
  case nonEmpty (DHash.toList controls) of
    Nothing -> SL.intE 0
    Just ((hGtt DSum.:=> _) :| tail) ->
      DHash.foldlWithKey (\nE gtt _ -> nE `SL.timesE` SB.groupSizeE gtt) (SB.groupSizeE hGtt) (DHash.fromList tail)


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
                  => Controls -> SL.VectorE -> SL.NamedDeclSpec t -> SL.CodeWriter (SL.UExpr t)
multiDimFromVec (Controls controls) v nds =
  case DHash.size controls of
    1 -> case nds of
      SL.NamedDeclSpec _ (SL.DeclSpec SL.StanVector _ _) -> SL.declareRHSNW nds v
      -> multiDimFromVec' controls v nds
    _ -> multiDimFromVec' controls v nds

multiDimFromVec' :: forall t md gq .
                 =>  Controls -> SL.VectorE -> SL.NamedDeclSpec t -> SL.CodeWriter (SL.UExpr t)
multiDimFromVec' controls v nds = do
  let sizeEs = fmap (\(DHash.Some gtt) -> SB.groupSizeE gtt) $ DHash.keys controls
      withVec :: SL.NamedDeclSpec t -> Vec.Vec n SL.EInt -> SL.CodeWriter (SL.UExpr t)
      vecSizesM :: Maybe (Vec.Vec (Dimension t) SL.IntE)= Vec.fromList sizeEs
  md <- SL.declareNW nds
  SL.addStmt $ SL.intVecLoops
-}





{-
matrixInsertZeroAtFunction :: SB.StanBuilderM md gq (SL.Function SL.EMat [SL.EMat, SL.EInt, SL.EInt])
matrixInsertZeroAtFunction = do
  let le = SL.boolOpE SL.SLT
      eq = SL.boolOpE SL.SEq
      f :: SL.Function SL.EMat [SL.EMat, SL.EInt, SL.EInt]
      f = SL.simpleFunction "matrix_insert_zero_at"
  SB.addFunctionOnce f (SL.Arg "m" :> SL.Arg "n" :> SL.Arg "m" :> TNil)
    $ \(m :> n :> m :> TNil)  -> SL.writerL $ do
    szE <- SL.declareRHSNW (SL.NamedDeclSpec "m" $ SL.intSpec []) $ SL.functionE SF.size (v :> TNil) `SL.plusE` SL.intE 1
    wzero <- SL.declareNW (SL.NamedDeclSpec "wz" $ SL.vectorSpec szE [])
--             $ SL.functionE SF.rep_vector (SL.realE 0 :> szE :> TNil)
    SL.addStmt $ SL.for "l" (SL.SpecificNumbered (SL.intE 1) szE)
      $ \l -> [SL.ifThenElse
                ((l `le` n, (wzero `SL.at` l) `SL.assign` (v `SL.at` l)) :|
                [(l `eq` n, (wzero `SL.at` l) `SL.assign` SL.realE 0)])
                ((wzero `SL.at` l) `SL.assign` (v `SL.at` (l `SL.minusE` SL.intE 1)))]
    return wzero
-}
