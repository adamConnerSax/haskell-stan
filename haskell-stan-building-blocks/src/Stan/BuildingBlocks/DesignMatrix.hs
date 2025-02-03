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
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use for_" #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

module Stan.BuildingBlocks.DesignMatrix
  (
    module Stan.BuildingBlocks.DesignMatrix
  )
where

import Prelude hiding (All)

import qualified Stan.Language as SL
import Stan.Language (TypedList(..))
import qualified Stan.Functions as SF
import Stan.Functions.Operators
import qualified Stan.Builder as SB
import qualified Stan.BuildingBlocks.Data as SBBD
import qualified Stan.BuildingBlocks.Misc as SBBM

import qualified Control.Foldl as FL
import qualified Control.Scanl as SL
import qualified Data.List as List
import qualified Data.Massiv.Array as MA
import qualified Data.Massiv.Vector as MV
import qualified Data.Massiv.Array.Numeric as MN
import qualified Data.Vector.Unboxed as V
import qualified Data.Type.Nat as DT
import Data.Type.Equality ((:~:)(..), TestEquality (..))

import Effectful (Eff)

data DesignMatrixRowPart r = DesignMatrixRowPart { dmrpName :: SL.VarName
                                                 , dmrpLength :: Int
                                                 , dmrpVecF :: r -> V.Vector Double
                                                 }

instance Contravariant DesignMatrixRowPart where
  contramap g (DesignMatrixRowPart n l f) = DesignMatrixRowPart n l (f . g)

-- a co-product
stackDesignMatrixRowParts :: DesignMatrixRowPart r1 -> DesignMatrixRowPart r2 -> Either Text (DesignMatrixRowPart (Either r1 r2))
stackDesignMatrixRowParts d1 d2 = do
  when (dmrpName d1 /= dmrpName d2) $ Left $ "stackDesignMatrixRowPart: Name mismatch! d1=" <> dmrpName d1 <> "; d2=" <> dmrpName d2
  when (dmrpLength d1 /= dmrpLength d2) $ Left $ "stackDesignMatrixRowPart: Length mismatch! l(d1)=" <> show (dmrpLength d1) <> "; l(d2)=" <> show (dmrpLength d2)
  pure $ DesignMatrixRowPart (dmrpName d1) (dmrpLength d1) (either (dmrpVecF d1) (dmrpVecF d2))
{-# INLINEABLE stackDesignMatrixRowParts #-}


data DesignMatrixRow r = DesignMatrixRow { dmName :: SL.VarName
                                         , dmParts :: [DesignMatrixRowPart r]
                                         }


instance Contravariant DesignMatrixRow where
  contramap g (DesignMatrixRow n dmrps) = DesignMatrixRow n $ fmap (contramap g) dmrps

stackDesignMatrixRows :: DesignMatrixRow r1 -> DesignMatrixRow r2 -> Either Text (DesignMatrixRow (Either r1 r2))
stackDesignMatrixRows dm1 dm2 = do
  when (dmName dm1 /= dmName dm2) $ Left $ "stackDesignMatrixRows: Name mismatch! dm1=" <> dmName dm1 <> "; dm2=" <> dmName dm2
  newParts <- traverse (uncurry stackDesignMatrixRowParts) $ zip (dmParts dm1) (dmParts dm2)
  return $ DesignMatrixRow (dmName dm1) newParts
{-# INLINEABLE stackDesignMatrixRows #-}

dmColIndexName :: DesignMatrixRow r -> Text
dmColIndexName dmr = dmName dmr <> "_Cols"
{-# INLINEABLE dmColIndexName #-}


rowLengthF :: FL.Fold (DesignMatrixRowPart r) Int
rowLengthF = FL.premap dmrpLength FL.sum
{-# INLINEABLE rowLengthF #-}

rowLength :: DesignMatrixRow r -> Int
rowLength = FL.fold rowLengthF . dmParts
{-# INLINEABLE rowLength #-}


rowFuncF :: FL.Fold (DesignMatrixRowPart r) (r -> V.Vector Double)
rowFuncF = appConcat . sequenceA <$> FL.premap dmrpVecF FL.list
  where appConcat g r = V.concat (g r)
{-# INLINEABLE rowFuncF #-}

designMatrixRowF :: DesignMatrixRow r -> (r -> V.Vector Double)
designMatrixRowF (DesignMatrixRow _ rowParts) = FL.fold rowFuncF rowParts
{-# INLINEABLE designMatrixRowF #-}

matrixFromRowData :: DesignMatrixRow r -> Maybe SL.IndexKey -> SB.MatrixRowFromData r
matrixFromRowData (DesignMatrixRow name rowParts) indexKeyM = SB.MatrixRowFromData name indexKeyM length' f
  where (length', f) = FL.fold ((,) <$> rowLengthF <*> rowFuncF) rowParts
{-# INLINEABLE matrixFromRowData #-}

designMatrixRowPartFromMatrixRowData :: SB.MatrixRowFromData r -> DesignMatrixRowPart r
designMatrixRowPartFromMatrixRowData (SB.MatrixRowFromData name _ n rowFunc) = DesignMatrixRowPart name n rowFunc
{-# INLINEABLE designMatrixRowPartFromMatrixRowData #-}
{-
combineRowFuncs :: Foldable f => f (Int, r -> V.Vector Double) -> (Int, r -> V.Vector Double)
combineRowFuncs rFuncs =
  let nF = FL.premap fst FL.sum
      fF = (\r -> V.concat . fmap ($ r)) <$> FL.premap snd FL.list
  in FL.fold ((,) <$> nF <*> fF) rFuncs
-}

newtype BEProduct2 a b = BEProduct2 { unBEProduct2 :: (a, b) } deriving stock (Show, Eq, Ord, Bounded)

instance (Bounded a, Enum a, Bounded b, Enum b) => Enum (BEProduct2 a b) where
  toEnum n = let nB = length (universe @b) in BEProduct2 (toEnum $ n `div` nB, toEnum $ n `mod` nB)
  fromEnum (BEProduct2 (a, b)) = let nB = length (universe @b) in nB * (fromEnum a) + fromEnum b

newtype BEProduct3 a b c = BEProduct3 { unBEProduct3 :: (a, b, c) } deriving stock (Show, Eq, Ord, Bounded)

toNested2 :: BEProduct3 a b c -> BEProduct2 a (BEProduct2 b c)
toNested2 (BEProduct3 (a, b, c)) = BEProduct2 (a, BEProduct2 (b, c))

fromNested2 :: BEProduct2 a (BEProduct2 b c) -> BEProduct3 a b c
fromNested2 (BEProduct2 (a, BEProduct2 (b, c))) = BEProduct3 (a, b, c)

instance  (Bounded a, Enum a, Bounded b, Enum b, Bounded c, Enum c) => Enum (BEProduct3 a b c) where
  toEnum = fromNested2 . toEnum
  fromEnum = fromEnum . toNested2

-- first argument, if set, will encode as that is all zeroes.
boundedEnumRowFunc :: forall r k . (Enum k, Bounded k, Eq k) => Maybe k -> (r -> k) -> (Int, r -> V.Vector Double)
boundedEnumRowFunc encodeAsZerosM rToKey = case numKeys of
  1 -> error "Single element enum given to boundedEnumRowFunc"
  2 -> binary
  _ -> nonBinary
  where
    binary = (1, \r -> V.singleton $ realToFrac $ if rToKey r == minBound then negate 1 :: Int else 1)
--    keys :: [k] = maybe id List.delete encodeAsZerosM universe
    numKeys = length (oneHotKeys encodeAsZerosM)
--    oneZero r x = if rToKey r == x then 1 else 0
    nonBinary = (numKeys, oneHotVector encodeAsZerosM . rToKey)
{-# INLINEABLE boundedEnumRowFunc #-}

oneHotKeys :: (Enum k, Bounded k, Eq k) => Maybe k -> [k]
oneHotKeys encodeAsZerosM =  maybe id List.delete encodeAsZerosM universe
{-# INLINEABLE oneHotKeys #-}

oneHotVector :: forall k.(Enum k, Bounded k, Eq k) => Maybe k -> k -> V.Vector Double
oneHotVector encodeAsZerosM k = V.fromList $ fmap (oneZero k) $ oneHotKeys encodeAsZerosM
  where
    oneZero l l' = if l == l' then 1 else 0
{-# INLINEABLE oneHotVector #-}

oneHotVectorMassiv :: forall k.(Enum k, Bounded k, Eq k) => Maybe k -> k -> MV.Vector MV.U Double
oneHotVectorMassiv encodeAsZerosM k = MA.compute $ MV.sfromList $ fmap (oneZero k) $ oneHotKeys encodeAsZerosM
  where
    oneZero l l' = if l == l' then 1 else 0
{-# INLINEABLE oneHotVectorMassiv #-}

boundedEnumRowPart :: (Enum k, Bounded k, Eq k) => Maybe k -> Text -> (r -> k) -> DesignMatrixRowPart r
boundedEnumRowPart encodeAsZerosM name f = DesignMatrixRowPart name n vf
  where (n, vf) = boundedEnumRowFunc encodeAsZerosM f
{-# INLINEABLE boundedEnumRowPart #-}

rowPartFromFunctions :: Text -> [r -> Double] -> DesignMatrixRowPart r
rowPartFromFunctions name fs = DesignMatrixRowPart name (length fs) toVec
  where
    toVec r = V.fromList $ fmap ($ r) fs
{-# INLINEABLE rowPartFromFunctions #-}

rowPartFromBoundedEnumFunctions :: forall k r.(Enum k, Bounded k, Eq k) => Maybe k -> Text -> (k -> r -> Double) -> DesignMatrixRowPart r
rowPartFromBoundedEnumFunctions encodeAsZerosM name f = DesignMatrixRowPart name vecSize (V.fromList . MV.stoList . sumScaledVecs)
  where keys :: [k] = universe
        vecSize :: Int = length keys - maybe 0 (const 1) encodeAsZerosM
        keyedVecs = zip keys $ fmap (oneHotVectorMassiv encodeAsZerosM) keys
        scaledVecs r = fmap (\(k, v) -> v MN..* f k r) keyedVecs
        sumScaledVecs r = FL.fold (FL.Fold (MN.!+!) (MA.compute $ MV.sreplicate (MA.Sz vecSize) 0) id) $ scaledVecs r
{-# INLINEABLE rowPartFromBoundedEnumFunctions #-}

-- adds matrix (name_dataSetName)
-- adds K_name (or given index) for col dimension (also <NamedDim name_Cols>)
-- row dimension should be N_dataSetName (which is <NamedDim dataSetName>)
-- E.g., if name="Design" and dataSetName="myDat"
-- In data
-- "Int N_myDat;" (was already there)
-- "Int K_Design;"
-- "matrix[N_myDat, K_Design] Design_myDat;"
-- with accompanying json
addDesignMatrix :: forall i d r es . (SB.StanJsonC i d es, SB.StanConstJsonC i d es)
                => SB.InputDataType i d -> SB.RowTypeTag r -> DesignMatrixRow r -> Maybe SL.IndexKey -> Eff es (SL.UExpr SL.EMat)
addDesignMatrix idt rtt dmr colIndexM = fst <$> SBBD.add2dMatrixData idt rtt (matrixFromRowData dmr colIndexM) Nothing Nothing
{-# INLINEABLE addDesignMatrix #-}


designMatrixColDimBinding ::  DesignMatrixRow r -> Maybe SL.IndexKey -> (SL.IndexKey, SL.UExpr SL.EInt)
designMatrixColDimBinding dmr indexKeyM = (colIndex, colExpr)
  where
    ik = fromMaybe (dmName dmr) indexKeyM
    colIndex = ik  <> "_Cols"
    colExpr = SL.namedE ("K_" <> ik) SL.SInt
{-# INLINEABLE designMatrixColDimBinding #-}

designMatrixIndexes :: DesignMatrixRow r -> [(DesignMatrixRowPart r, Int, Int)]
designMatrixIndexes (DesignMatrixRow _ dmps)= SL.scan rowPartScan dmps where
  rowPartScanStep rp = do
    curIndex <- get
    put $ curIndex + dmrpLength rp
    return (rp, dmrpLength rp, curIndex)
  rowPartScan = SL.Scan rowPartScanStep 1

designMatrixPartSizeName :: DesignMatrixRow r -> DesignMatrixRowPart r -> SL.VarName
designMatrixPartSizeName dmr dmrp = "S_" <> dmName dmr <> "_" <> dmrpName dmrp
{-# INLINEABLE designMatrixPartSizeName #-}

designMatrixPartIndexName :: DesignMatrixRow r -> DesignMatrixRowPart r -> SL.VarName
designMatrixPartIndexName dmr dmrp = "I_" <> dmName dmr <> "_" <> dmrpName dmrp
{-# INLINEABLE designMatrixPartIndexName #-}


-- declares S_DesignName_PartName (size of part) and I_DesignName_PartName (starting index of part) and for all parts of design matrix row
addDesignMatrixIndexes :: forall i d r es . SB.StanConstJsonC i d es
                       => SB.InputDataType i d -> DesignMatrixRow r -> Eff es [(DesignMatrixRowPart r, SL.UExpr SL.EInt, SL.UExpr SL.EInt)]
addDesignMatrixIndexes idt dmr = do
  let addEach (rp, gSize, gStart) = do
--        let sizeName = dmName dmr <> "_" <> gName
        se <- SB.addFixedIntJson SB.ErrIfDuplicate idt (designMatrixPartSizeName dmr rp) Nothing gSize
        ie <- SB.addFixedIntJson SB.ErrIfDuplicate idt (designMatrixPartIndexName dmr rp) Nothing gStart
        pure (rp, se, ie)
  traverse addEach $ designMatrixIndexes dmr

splitToGroupVar :: forall t r es . (SB.StanCodeC es, SL.IsContainer t, SL.GenSType t)
                => (DesignMatrixRowPart r, SL.UExpr SL.EInt, SL.UExpr SL.EInt)
                -> SL.UExpr t
                -> SL.VarName
                -> Eff es (SL.UExpr t)
splitToGroupVar (dmrp, se, ie) tse sn = do
  let newVarName = sn <> "_" <> dmrpName dmrp
      splitVarRowsE = SF.size tse
      segment :: SL.UExpr SL.ECVec -> SL.UExpr SL.ECVec
      segment x = SF.segment x ie se --  $ SB.var x :| [SB.name index, namedDimE sizeName]
      block x = SF.block x (SL.intE 1) ie splitVarRowsE se

  case SL.genSType @t of
    SL.SCVec -> SB.addFromCodeWriter $ SL.declareRHSNW (SL.NamedDeclSpec newVarName $ SL.vectorSpec se) $ segment tse
    SL.SArray sn' SL.SCVec -> case testEquality sn' (DT.SS @DT.Nat0) of
      Just Refl -> do
        xe :: SL.UExpr (SL.EArray1 SL.ECVec) <- SB.addFromCodeWriter $ SL.declareNW (SL.NamedDeclSpec newVarName $ SL.array1Spec splitVarRowsE (SL.vectorSpec se))
        SB.addStmtToCode
          $ SL.for "k" (SL.SpecificNumbered (SL.intE 1) splitVarRowsE)
          $ \ke -> let atk = SL.sliceE SL.s0 ke
                   in atk xe SL.|=| segment (atk tse)
        pure xe
      _ -> SB.buildError "DesignMatrix.splitToGroupVar: Can only split vectors, 1d arrays of vectors, or matrices."
    SL.SMat -> SB.addFromCodeWriter $ SL.declareRHSNW (SL.NamedDeclSpec newVarName $ SL.matrixSpec splitVarRowsE se) $ block tse
    _ -> SB.buildError "DesignMatrix.splitToGroupVar: Can only split vectors, 1d arrays of vectors, or matrices."

-- take a Stan vector, array, or matrix indexed by this design row
-- and split into the parts for each group
-- this doesn't depend on r
-- Do we want to
-- 1. Check dimensions? Don't know how from Haskell side.
-- 2. Should the name prefix here come from the design matrix name?
splitToGroupVars :: (SB.StanCodeC es, SL.IsContainer t, SL.GenSType t)
                 => DesignMatrixRow r -> SL.UExpr t -> Maybe SL.VarName -> Eff es [SL.UExpr t]
splitToGroupVars dmr tse nM =
  let n = fromMaybe (dmName dmr) nM
  in traverse (\(dmrp, k, l) -> splitToGroupVar (dmrp, SL.intE k, SL.intE l) tse n) $ designMatrixIndexes dmr
{-
  let designColName = n <> "_Cols"
  case st of
    SB.StanVector d -> when (d /= SB.NamedDim designColName)
      $ SB.stanBuildError $ "DesignMatrix.splitTogroupVars: vector to split has wrong dimension: " <> show d
    SB.StanArray _ (SB.StanVector d) -> when (d /= SB.NamedDim designColName)
      $ SB.stanBuildError $ "DesignMatrix.splitTogroupVars: vectors in array of vectors to split has wrong dimension: " <> show d
    SB.StanMatrix (d, _)  -> when (d /= SB.NamedDim designColName)
      $ SB.stanBuildError $ "DesignMatrix.splitTogroupVars: matrix to split has wrong row-dimension: " <> show d
  traverse (\(g, _, _) -> splitToGroupVar n g v) $ designMatrixIndexes dmr
-}

data DMParameterization = DMCentered | DMNonCentered deriving stock (Show, Eq)

{-
addDMParametersAndPriors :: (Typeable md, Typeable gq)
                         => DesignMatrixRow r
                         -> SB.GroupTypeTag k -- exchangeable contexts
                         -> SL.StanName -- name for beta parameter (so we can use theta if QR)
                         -> DMParameterization
                         -> (SL.DensityWithArgs SL.ECVec, SL.DensityWithArgs SL.ECVec, SL.DensityWithArgs SL.ESqMat) -- priors for mu and tau and lkj parameter
                         -> Maybe Text -- suffix for varnames
                         -> SB.StanBuilderM md gq (DAG.ParameterTag SL.ECVec -- alpha
                                                  , DAG.ParameterTag SL.EMat -- beta
                                                  , DAG.ParameterTag SL.ECVec -- mu
                                                  , DAG.ParameterTag SL.ECVec -- tau
                                                  , DAG.ParameterTag SL.ESqMat -- corr
                                                  )
addDMParametersAndPriors dmr gtt betaName parameterization (muPrior, tauPrior, lkjPrior) = do



addDMParametersAndPriors' :: (Typeable md, Typeable gq)
                         => DesignMatrixRow r
                         -> SB.GroupTypeTag k -- exchangeable contexts
                         -> SL.StanName -- name for beta parameter (so we can use theta if QR)
                         -> DMParameterization
                         -> (SL.DensityWithArgs SL.ECVec, SL.DensityWithArgs SL.ECVec, SL.DensityWithArgs SL.ESqMat) -- priors for mu and tau and lkj parameter
                         -> Maybe Text -- suffix for varnames
                         -> SB.StanBuilderM md gq (DAG.ParameterTag SL.ECVec -- alpha
                                                  , DAG.ParameterTag SL.EMat -- beta
                                                  , DAG.ParameterTag SL.ECVec -- mu
                                                  , DAG.ParameterTag SL.ECVec -- tau
                                                  , DAG.ParameterTag SL.ESqMat -- corr
                                                  )
addDMParametersAndPriors' dmr gtt betaName parameterization (muPrior, tauPrior, lkjPrior) = do
  let dmDimName = designMatrixName <> "_Cols"
      dmDim = SB.NamedDim dmDimName
      dmVec = SB.StanVector dmDim
      vecDM = SB.vectorizedOne dmDimName
      gName =  SB.taggedGroupName g
      gDim = SB.NamedDim gName
      gVec = SB.StanVector gDim
      vecG = SB.vectorizedOne gName
      s = fromMaybe "" mS
      normal x = SB.normal Nothing (SB.scalar $ show x)
      dmBetaE dm beta = vecDM $ SB.function "dot_product" (SB.var dm :| [SB.var beta])
      lkjPriorE = SB.function "lkj_corr_cholesky" (SB.scalar (show lkjParameter) :| [])

  (alphaRaw, muAlpha, sigmaAlpha, mu, tau, lCorr, betaRaw) <- do
    alphaRaw' <- case parameterization of
      DMCentered -> SB.stanDeclare ("alpha" <> s) gVec ""
      DMNonCentered -> SB.stanDeclare ("alpha_raw" <> s) gVec ""
    muAlpha' <- SB.stanDeclare ("mu_alpha" <> s) SB.StanReal ""
    sigmaAlpha' <- SB.stanDeclare ("sigma_alpha" <> s) SB.StanReal "<lower=0>"
    mu' <- SB.stanDeclare ("mu" <> s) dmVec ""
    tau' <- SB.stanDeclare ("tau" <> s) dmVec "<lower=0>"
    lCorr' <- SB.stanDeclare ("L" <> s) (SB.StanCholeskyFactorCorr dmDim) ""
    betaRaw' <- case parameterization of
      DMCentered -> SB.stanDeclare (betaName <> s) (SB.StanMatrix (dmDim, gDim)) ""
      DMNonCentered -> SB.stanDeclare (betaName <> s <> "_raw") (SB.StanMatrix (dmDim, gDim)) ""
    return (alphaRaw', muAlpha', sigmaAlpha', mu', tau', lCorr', betaRaw')
  let dpmE = SB.function "diag_pre_multiply" (SB.var tau :| [SB.var lCorr])
      repMu = SB.function "rep_matrix" (SB.var mu :| [SB.indexSize gName])
  beta <- case parameterization of
    DMCentered -> return betaRaw
    DMNonCentered -> SB.inBlock SB.SBTransformedParameters $
      SB.stanDeclareRHS (betaName <> s) (SB.StanMatrix (dmDim,gDim)) ""
        $ vecG $ vecDM $ repMu `SB.plus` (dpmE `SB.times` SB.var betaRaw)
  alpha <- case parameterization of
    DMCentered -> return alphaRaw
    DMNonCentered -> SB.inBlock SB.SBTransformedParameters $
      SB.stanDeclareRHS ("alpha" <> s) gVec ""
      $ vecG $ SB.var muAlpha `SB.plus` (SB.var sigmaAlpha `SB.times` SB.var alphaRaw)
  SB.inBlock SB.SBModel $ do
    case parameterization of
      DMCentered -> do
        SB.addExprLines "addDMParametersAnsPriors"
          [vecDM $ SB.var betaRaw `SB.vectorSample` SB.function "multi_normal_cholesky" (SB.var mu :| [dpmE])
          , vecG $ SB.var alphaRaw `SB.vectorSample` SB.function "normal" (SB.var muAlpha :| [SB.var sigmaAlpha])]
      DMNonCentered ->
--        SB.stanForLoopB "g" Nothing gName
        SB.addExprLines "addDMParametersAndPriors"
        [vecG $ vecDM $ SB.function "to_vector" (one $ SB.var betaRaw) `SB.vectorSample` SB.stdNormal
        , vecG $ SB.var alphaRaw `SB.vectorSample` SB.stdNormal]

    SB.addExprLines "addParametersAndPriors" $
      [ SB.var muAlpha `SB.vectorSample` muPrior
      , SB.var sigmaAlpha `SB.vectorSample` tauPrior
      , vecDM $ SB.var mu `SB.vectorSample` muPrior
      , vecDM $ SB.var tau `SB.vectorSample` tauPrior
      , vecDM $ SB.var lCorr `SB.vectorSample` lkjPriorE
      ]
  pure (alpha, beta, mu, tau, lCorr)
-}
data DMStandardization = DMCenterOnly | DMCenterAndScale

fixSDZeroFunction :: SB.StanFunctionsC es => Eff es (SL.Function SL.EReal '[SL.EReal])
fixSDZeroFunction =  do
  let f :: SL.Function SL.EReal '[SL.EReal]
      f = SL.simpleFunction "fixSDZero"
  SB.addFunctionOnce f (SL.Arg "x" :> TNil)
    $ \(x :> TNil) -> SL.cwStmt $ pure $ SL.condE (x |==| (SL.realE 0)) (SL.realE 1) x

shiftDataMatrixFunction :: SB.StanFunctionsC es => Eff es (SL.Function SL.EMat '[SL.EMat, SL.ECVec])
shiftDataMatrixFunction =  do
  let f :: SL.Function SL.EMat '[SL.EMat, SL.ECVec]
      f = SL.simpleFunction "shiftDataMatrix"
  SB.addFunctionOnce f (SL.DataArg "m" :> SL.DataArg "means" :> TNil)
    $ \(m :> means :> TNil) -> SL.cwStmt $ do
    newMatrix <- SL.declareNW (SL.NamedDeclSpec "shifted" $ SL.matrixSpec (SF.rows m) (SF.cols m))
    SL.addStmt $ SL.for "k" (SL.SpecificNumbered (SL.intE 1) $ SF.cols m)
      $ \ke ->
          let colk :: SL.UExpr q -> SL.UExpr (SL.Sliced SL.N1 q)
              colk = SL.sliceE SL.s1 ke
              atk = SL.sliceE SL.s0 ke
          in colk newMatrix SL.|=| (colk m |-| atk means)
    return newMatrix


shiftAndScaleDataMatrixFunction :: SB.StanFunctionsC es => Eff es (SL.Function SL.EMat '[SL.EMat, SL.ECVec, SL.ECVec])
shiftAndScaleDataMatrixFunction =  do
  let f :: SL.Function SL.EMat '[SL.EMat, SL.ECVec, SL.ECVec]
      f = SL.simpleFunction "shiftAndScaleDataMatrix"
  SB.addFunctionOnce f (SL.DataArg "m" :> SL.DataArg "means" :> SL.DataArg "sds" :> TNil)
    $ \(m :> means :> sds :> TNil) -> SL.cwStmt $ do
    newMatrix <- SL.declareNW (SL.NamedDeclSpec "shiftedAndScaled" $ SL.matrixSpec (SF.rows m) (SF.cols m))
    SL.addStmt $ SL.for "k" (SL.SpecificNumbered (SL.intE 1) $ SF.cols m)
      $ \ke ->
          let colk :: SL.UExpr q -> SL.UExpr (SL.Sliced SL.N1 q)
              colk = SL.sliceE SL.s1 ke
              atk = SL.sliceE SL.s0 ke
          in colk newMatrix SL.|=| ((colk m |-| atk means) |/| atk sds)
    return newMatrix

centerDataMatrix :: (SB.StanFunctionsC es, SB.StanCodeC es)
                 => DMStandardization
                 -> SL.UExpr SL.EMat -- matrix
                 -> Maybe (SL.UExpr SL.ECVec)
                 -> SL.VarName -- prefix for names
                 -> Eff es (SL.UExpr SL.EMat -- standardized matrix, X - row_mean(X) or (X - row_mean(X))/row_stddev(X)
                           , SB.InputDataType i d -> SL.UExpr SL.EMat -> SL.VarName -> Eff es (SL.UExpr SL.EMat) -- \Y -> standardized Y (via mean/var of X)
                           )
centerDataMatrix dms m mwgtsV namePrefix = do
  vecMVF <- case mwgtsV of
    Nothing -> do
      mvF <- SBBM.unWeightedMeanVarianceFunction
--      let dummyVecE = SL.namedE "dummyVec" SL.SCVec
      return $ \mc -> SL.functionE mvF (mc :> TNil)
    Just wgtsV -> do
      mvF <- SBBM.weightedMeanVarianceFunction
      return $ \mc -> SL.functionE mvF (wgtsV :> mc :> TNil)
  SB.inBlock SL.SBTransformedData $ case dms of
    DMCenterAndScale -> do
      fixSDZero <- fixSDZeroFunction
      mVec <- SB.addFromCodeWriter $ SL.declareNW $ SL.NamedDeclSpec (namePrefix <> "_means") $ SL.vectorSpec (SF.cols m)
      sVec <- SB.addFromCodeWriter $ SL.declareNW $ SL.NamedDeclSpec (namePrefix <> "_variances") $ SL.vectorSpec (SF.cols m)
      SB.addStmtToCode
        $ SL.for "k" (SL.SpecificNumbered (SL.intE 1) $ SF.cols m)
        $ \ke -> SL.cwStmt_ $ do
        let kCol = SL.sliceE SL.s1 ke
            atk = SL.sliceE SL.s0 ke
        mv <- SL.declareRHSNW (SL.NamedDeclSpec "mv" $ SL.tuple2Spec SL.realSpec SL.realSpec) $ vecMVF (kCol m)
        SL.addStmt $ atk mVec SL.|=| (SL.fstRef mv)
        SL.addStmt $ atk sVec SL.|=| SL.functionE fixSDZero (SF.sqrt (SL.sndRef mv) :> TNil)
      shiftAndScaleF <- shiftAndScaleDataMatrixFunction
      let stdize x = SL.functionE shiftAndScaleF (x :> mVec :> sVec :> TNil)
      mStd <- SB.addFromCodeWriter
              $ SL.declareRHSNW (SL.NamedDeclSpec (namePrefix <> "_standardized") $ SL.matrixSpec (SF.rows m) (SF.cols m))
              $ stdize m
      let centerF idt m' n = do
            SB.inBlock (SB.caseInputDataType SL.SBTransformedData SL.SBTransformedDataGQ idt) $ SB.addFromCodeWriter
              $ SL.declareRHSNW (SL.NamedDeclSpec n $ SL.matrixSpec (SF.cols m') (SF.cols m')) $ stdize m'
      return (mStd, centerF)
    DMCenterOnly -> do
      mVec <- SB.addFromCodeWriter $ SL.declareNW $ SL.NamedDeclSpec (namePrefix <> "_means") $ SL.vectorSpec (SF.cols m)
      SB.addStmtToCode
        $ SL.for "k" (SL.SpecificNumbered (SL.intE 1) $ SF.cols m)
        $ \ke -> SL.cwStmt_ $ do
        let kCol = SL.sliceE SL.s1 ke
            atk = SL.sliceE SL.s0 ke
        mv <- SL.declareRHSNW (SL.NamedDeclSpec "mv" $ SL.tuple2Spec SL.realSpec SL.realSpec) $ vecMVF (kCol m)
        SL.addStmt $ atk mVec SL.|=| (SL.fstRef mv)
      shiftF <- shiftDataMatrixFunction
      let centered x = SL.functionE shiftF (x :> mVec :> TNil)
      mCentered <- SB.addFromCodeWriter
                   $ SL.declareRHSNW (SL.NamedDeclSpec (namePrefix <> "_centered") $ SL.matrixSpec (SF.rows m) (SF.cols m))
                   $ centered m
      let centerF idt m' n = do
            SB.inBlock (SB.caseInputDataType SL.SBTransformedData SL.SBTransformedDataGQ idt)
              $ SB.addFromCodeWriter
              $ SL.declareRHSNW (SL.NamedDeclSpec n $ SL.matrixSpec (SF.rows m') (SF.cols m')) $ centered m'
      pure (mCentered, centerF)



-- take a matrix x and return (thin) Q, R and inv(R)
-- as Q_x, R_x, invR_x
-- see https://mc-stan.org/docs/2_28/stan-users-guide/QR-reparameterization.html
thinQR :: forall t es . (SB.StanCodeC es, SL.GenSType t, SL.TypeOneOf t [SL.ECVec, SL.EMat, SL.EArray1 SL.ECVec])
       => SL.MatrixE -- matrix of predictors
       -> SL.VarName -- names prefix
       -> Maybe (SL.UExpr t, SL.NamedDeclSpec t) -- theta and name for beta
       -> Eff es (SL.UExpr SL.EMat, SL.UExpr SL.EMat, SL.UExpr SL.EMat, Maybe (SL.UExpr t))
thinQR xE xName mThetaBeta = do
  (q, r, rI) <- SB.inBlock SL.SBTransformedData $ do
    qE  <- SB.addFromCodeWriter $ SL.declareRHSNW (SL.NamedDeclSpec ("Q_" <> xName) $ SL.matrixSpec (SF.rows xE) (SF.cols xE))
           $ SF.qr_thin_Q xE |*| SF.sqrt (SF.rows xE |-| SL.realE 1)
    rE  <- SB.addFromCodeWriter $ SL.declareRHSNW (SL.NamedDeclSpec ("R_" <> xName) $ SL.matrixSpec (SF.cols xE) (SF.cols xE))
           $ SF.qr_thin_R xE |/| SF.sqrt (SF.rows xE |-| SL.realE 1)
    rInvE <- SB.addFromCodeWriter $ SL.declareRHSNW (SL.NamedDeclSpec ("invR_" <> xName) $ SL.matrixSpec (SF.cols xE) (SF.cols xE))
             $ SF.inverse rE
    return (qE, rE, rInvE)
  mBeta <-  SB.inBlock SL.SBGeneratedQuantities $ case mThetaBeta of
    Nothing -> return Nothing
    Just (theta, betaNDS) -> fmap Just $ case SL.genSType @t of
      SL.SMat -> SB.addFromCodeWriter $ SL.declareRHSNW betaNDS $ rI |*| theta
      SL.SCVec -> SB.addFromCodeWriter $ SL.declareRHSNW betaNDS $ rI |*| theta
      SL.SArray sn SL.SCVec -> case testEquality sn (DT.SS @DT.Nat0) of
        Just Refl -> do
          let arrSizeE = SF.size theta
          SB.addFromCodeWriter $ do
            beta <- SL.declareNW betaNDS
            SL.addStmt $ SL.for "j" (SL.SpecificNumbered (SL.intE 0) arrSizeE)
                               $ \j -> let atj = SL.sliceE SL.s0 j in atj beta `SL.assign` (rI `SL.timesE` atj theta)
            pure beta

        Nothing -> SB.buildError $ "DesignMatrix.thinQR array of dimension other than 1 given for theta."
  return (q, r, rI, mBeta)
