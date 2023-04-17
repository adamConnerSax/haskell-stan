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
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use for_" #-}
{-# HLINT ignore "Use camelCase" #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeFamilyDependencies #-}

module Stan.ModelBuilder.BuildingBlocks.CovarianceStructure
  (
    module Stan.ModelBuilder.BuildingBlocks.CovarianceStructure
  )
where

import Prelude hiding (Nat)
import qualified Stan.ModelBuilder.TypedExpressions.Types as TE
import Stan.ModelBuilder.TypedExpressions.TypedList (TypedList(..))
import qualified Stan.ModelBuilder.TypedExpressions.TypedList as TL
import qualified Stan.ModelBuilder.TypedExpressions.Statements as TE
import qualified Stan.ModelBuilder.TypedExpressions.Indexing as TE
import qualified Stan.ModelBuilder.TypedExpressions.Operations as TE
import qualified Stan.ModelBuilder.TypedExpressions.StanFunctions as SF
import qualified Stan.ModelBuilder.TypedExpressions.DAGTypes as DAG
import qualified Stan.ModelBuilder.TypedExpressions.DAG as DAG
import qualified Stan.ModelBuilder as SB
import qualified Stan.ModelBuilder.Distributions as SMD
import qualified Stan.ModelBuilder.BuildingBlocks as SBB
import qualified Stan.ModelBuilder.BuildingBlocks.ArrayHelpers as SBBA

import qualified Data.Vec.Lazy as Vec
import qualified Data.Type.Nat as DT
import Data.Type.Equality (type (:~:)(..))

import Prelude hiding (sum, All)
import qualified Data.Dependent.HashMap as DHash
import qualified Data.Vector.Unboxed as VU
import qualified Stan.ModelConfig as SB
import Stan.ModelBuilder.BuilderTypes (dataSetSizeName)

-- rows x cols matrix of parameters. Perhaps w Cholesky factor.
data MatrixCovarianceStructure = Diagonal | Cholesky TE.SqMatrixE

data Centering = Centered | NonCentered

-- A singleton to code return type
--data ReturnType t where
--  SingleMatrix :: SingleMatrix TE.MatrixE
--  ArrayOfMatrices :: TE.IntE -> ReturnType (TE.EArray1 TE.EMat)

type ParamC t = (TE.TypeOneOf t [TE.EMat, TE.EArray1 TE.EMat], TE.GenSType t)
type FParamC t = (TE.TypeOneOf t [TE.ECVec, TE.EArray1 TE.ECVec], TE.GenSType t)

type family FlatParamT t = ft | ft -> t where
  FlatParamT TE.EMat = TE.ECVec
  FlatParamT (TE.EArray (DT.S n) TE.EMat) = TE.EArray (DT.S n) TE.ECVec

{-
type family UnFlatParamT t where
  UnFlatParamT TE.ECVec = TE.EMat
  UnFlatParamT (TE.EArray (DT.S n) TE.ECVec) = TE.EArray (DT.S n) TE.EMat

--invProof :: (Un)
-}

type ArrayMatDims n = (Vec.Vec n TE.IntE, Vec.Vec DT.Nat2 TE.IntE)

arrayMatDims :: DT.SNatI m => Vec.Vec (m `DT.Plus` DT.Nat2) TE.IntE -> ArrayMatDims m
arrayMatDims = Vec.split

makeVecArraySpec :: (DT.SNatI (DT.S m)
                    , forall f. TE.VecToTListC f m
                    , forall f. TE.TListToVecC f m
                    )
                 => [TE.VarModifier TE.UExpr (TE.ScalarType TE.EReal)]
                 -> Vec.Vec (DT.S m) TE.IntE
                 -> TE.IntE
                 -> TE.IntE
                 -> TE.DeclSpec (TE.EArray (DT.S m) TE.ECVec)
makeVecArraySpec vms aDims rowsE colsE = TE.arraySpec DT.snat aDims $ TE.vectorSpec (rowsE `TE.timesE`colsE) vms

flatDS :: forall t . TE.DeclSpec t -> TE.DeclSpec (FlatParamT t)
flatDS ds =
  case ds of
    TE.DeclSpec TE.StanMatrix (rowsE Vec.::: colsE Vec.::: Vec.VNil) vms ->
      TE.vectorSpec (rowsE `TE.timesE` colsE) vms
    TE.ArraySpec n@DT.SS arrDims mds ->
      case mds of
        TE.DeclSpec TE.StanMatrix (rowsE Vec.::: colsE Vec.::: Vec.VNil) vms ->
          DT.withSNat n $ makeVecArraySpec vms arrDims rowsE colsE
    _ -> error "flatDS: Given type of something other than matrix or array of matrices!"

--flatNDS :: ParamC t => TE.NamedDeclSpec t -> TE.NamedDeclSpec (FlatParamT t)
--flatNDS nds = TE.NamedDeclSpec (TE.declName nds <> "_flat") $ flatDS $ TE.decl nds

flattenLoop :: forall n .
               (TL.SameTypedListToVecF TE.UExpr TE.EInt n
               , TL.VecToSameTypedListF TE.VarAndForType TE.EInt n
               , DT.SNatI n
               )
            => Text
            -> Vec.Vec (DT.S n) TE.IntE
            -> TE.UExpr (TE.EArray (DT.S n) TE.ECVec)
            -> TE.UExpr (TE.EArray (DT.S n) TE.EMat)
            -> TE.CodeWriter ()
flattenLoop counterPrefix arrDims aVecE aMatE = SBBA.applyToArrayOf counterPrefix (\x -> TE.functionE SF.to_vector (x :> TNil)) arrDims aMatE aVecE

flattenCW :: (ParamC t)
          => TE.StanName -> TE.DeclSpec t -> TE.UExpr t -> TE.CodeWriter (TE.UExpr (FlatParamT t))
flattenCW sn ds e =
  let flatten x =  TE.functionE SF.to_vector (x :> TNil)
  in case ds of
    TE.DeclSpec TE.StanMatrix _ _ -> pure $ flatten e
    TE.ArraySpec DT.SS arrDims mds -> do
      case mds of
        TE.DeclSpec TE.StanMatrix _ _ -> do
          fv <- TE.declareNW $ TE.NamedDeclSpec (sn <> "_flat") $ flatDS ds
          flattenLoop "k" arrDims fv e
          pure fv

makeMatArraySpec :: (DT.SNatI (DT.S m)
                    , forall f. TE.VecToTListC f m
                    , forall f. TE.TListToVecC f m
                    )
                 => [TE.VarModifier TE.UExpr (TE.ScalarType TE.EReal)]
                 -> Vec.Vec (DT.S m) TE.IntE
                 -> TE.IntE
                 -> TE.IntE
                 -> TE.DeclSpec (TE.EArray (DT.S m) TE.EMat)
makeMatArraySpec vms aDims rowsE colsE = TE.arraySpec DT.snat aDims $ TE.matrixSpec rowsE colsE vms


unFlatDS :: forall t . TE.DeclSpec t -> TE.DeclSpec t
unFlatDS ds =
  case ds of
    TE.DeclSpec TE.StanMatrix (rowsE Vec.::: colsE Vec.::: Vec.VNil) vms -> TE.matrixSpec rowsE colsE vms
    TE.ArraySpec n@DT.SS arrDims mds ->
      case mds of
        TE.DeclSpec TE.StanMatrix (rowsE Vec.::: colsE Vec.::: Vec.VNil) vms ->
          DT.withSNat n $ makeMatArraySpec vms arrDims rowsE colsE
    _ -> error "flatDS: Given type of something other than matrix or array of matrices!"


unFlattenLoop :: forall n .
                 (TL.SameTypedListToVecF TE.UExpr TE.EInt n
                 , TL.VecToSameTypedListF TE.VarAndForType TE.EInt n
                 , DT.SNatI n
                 )
              => Text
              -> TE.IntE
              -> TE.IntE
              -> Vec.Vec (DT.S n) TE.IntE
              -> TE.UExpr (TE.EArray (DT.S n) TE.EMat)
              -> TE.UExpr (TE.EArray (DT.S n) TE.ECVec)
              -> TE.CodeWriter ()
unFlattenLoop counterPrefix rowsE colsE arrDims ufE fE = SBBA.applyToArrayOf counterPrefix (\x -> TE.functionE SF.vecToMatrix (x :> rowsE :> colsE :> TNil)) arrDims fE ufE


unFlattenCW :: TE.StanName -> TE.DeclSpec t -> TE.UExpr (FlatParamT t) -> TE.CodeWriter (TE.UExpr t)
unFlattenCW sn ds e =
  let unFlatten x rowsE colsE =  TE.functionE SF.vecToMatrix (x :> rowsE :> colsE :> TNil)
  in case ds of
    TE.DeclSpec TE.StanMatrix (rowsE Vec.::: colsE Vec.::: Vec.VNil) _ -> pure $ unFlatten e rowsE colsE
    TE.ArraySpec DT.SS arrDims mds -> do
      case mds of
        TE.DeclSpec TE.StanMatrix (rowsE Vec.::: colsE Vec.::: Vec.VNil) _ -> do
          fv <- TE.declareNW $ TE.NamedDeclSpec (sn <> "_unflat") $ unFlatDS ds  -- this is wrong? (EArray (S 'n1) ECVec ~ EArray n ECVec) rather than (EArray (S n) ECVec)
          unFlattenLoop "k" rowsE colsE arrDims fv e
          pure fv

unFlattenACW :: TE.DeclSpec t -> TE.UExpr (FlatParamT t) -> TE.UExpr t -> TE.CodeWriter ()
unFlattenACW ds fe e = do
  let unFlatten x rowsE colsE =  TE.functionE SF.vecToMatrix (x :> rowsE :> colsE :> TNil)
  case ds of
    TE.DeclSpec TE.StanMatrix (rowsE Vec.::: colsE Vec.::: Vec.VNil) _ -> TE.addStmt (e `TE.assign` unFlatten fe rowsE colsE)
    TE.ArraySpec DT.SS arrDims mds -> case mds of
      TE.DeclSpec TE.StanMatrix (rowsE Vec.::: colsE Vec.::: Vec.VNil) _ -> unFlattenLoop "k" rowsE colsE arrDims e fe
    _ -> pure ()


nonCenteredFlat :: TE.StanName
                -> TE.DeclSpec t
                -> TE.UExpr (FlatParamT t)
                -> TE.MatrixE
                -> TE.UExpr (FlatParamT t)
                -> TE.CodeWriter (TE.UExpr (FlatParamT t))
nonCenteredFlat givenName ds flatMu sigmaE rawFlatE = do
  let qfd m v = TE.functionE SF.quadFormDiag (m :> v :> TNil)
      flatten m = TE.functionE SF.to_vector (m :> TNil) -- column major
      flatSigma = flatten sigmaE
      eltMultiply = TE.binaryOpE (TE.SElementWise TE.SMultiply)
      ncfF :: TE.ExprList '[TE.ECVec, TE.ECVec] -> TE.VectorE
      ncfF (muFlat :> rawFlat :> TNil) = muFlat `TE.plusE` (rawFlat `eltMultiply` flatSigma)
  case ds of
    TE.DeclSpec TE.StanMatrix _ _ -> pure $ ncfF (flatMu :> rawFlatE :> TNil)
    TE.ArraySpec DT.SS arrDims mds -> case mds of
      TE.DeclSpec TE.StanMatrix _ _ -> do
        ncfE <- TE.declareNW $ TE.NamedDeclSpec (givenName <> "_ncf") $ flatDS ds
        SBBA.applyToArrayOf' "k" ncfF arrDims (SBBA.ArrayOf flatMu :> SBBA.ArrayOf rawFlatE :> TNil) ncfE
        pure ncfE


zeroVec :: TE.IntE -> TE.VectorE
zeroVec lE = TE.functionE SF.rep_vector(TE.realE 0 :> lE :> TNil)

-- lordy. Look at those constraints!
arrayOfZeroVecs :: (TL.SameTypeList TE.EInt n ~ SF.NInts n
                   , TL.VecToSameTypedListF TE.UExpr TE.EInt n
                   , TL.GenTypeList (SF.NInts n)
                   , DT.SNatI n)
                => Vec.Vec (DT.S n) TE.IntE -> TE.IntE -> TE.UExpr (TE.EArray (DT.S n) TE.ECVec)
arrayOfZeroVecs arrDims lE = TE.functionE SF.rep_array (zeroVec lE :> TL.vecToSameTypedList arrDims)

{-
stdNormalRaw :: MatrixCovarianceStructure -> TE.DeclSpec t -> TE.UExpr (FlatParamT t) -> TE.CodeWriter ()
stdNormalRaw cs ds rawFlatE = do
  let sampleF e = case cs of
        Diagonal -> TE.sample e SF.std_normal TNil
        Cholesky cf -> TE.sample e SF.multi_normal_cholesky(zero, ) TNil
-}
{-
data ParamMat t where
  SingleParam :: TE.MatrixE -> ParamMat TE.EMat
  ArrayParam :: TE.ArrayE TE.EMat -> ParamMat (TE.EArray1 TE.EMat)
-}
{-
matrixMultiNormalParameter :: forall t md gq n .
                              (ParamC t
                              ,SF.MultiNormalDensityC (FlatParamT t)
                              )
                           => MatrixCovarianceStructure
                           -> Centering
                           -> DAG.Parameter t
                           -> DAG.Parameter TE.EMat
                           -> TE.NamedDeclSpec t
                           -> SB.StanBuilderM md gq (TE.UExpr t)
matrixMultiNormalParameter cs cent muP sigmaP nds = do
  let flatten m = TE.functionE SF.to_vector (m :> TNil) -- column major
      multiNormalC x muFlat lSigma = TE.sample x SF.multi_normal_cholesky (muFlat :> lSigma :> TNil)
      multiNormalD x muFlat dSigma = TE.sample x SF.multi_normal (muFlat :> dSigma :> TNil)

  p <- DAG.addBuildParameter $ DAG.UntransformedP nds [] TNil (\_ _ -> pure ())
  let fDS = flatDS (TE.decl nds)
      givenName = TE,declName nds
      rawNDS = TE.NamedDeclSpec (TE.declName nds <> "_raw") fDS
      justDeclare _ = DAG.DeclCodeF $ const $ pure ()
      sampleF e fm s = case cs of
        Diagonal ->
          let sm = TE.functionE SF.diag (flatten s :> TNil)
          in multiNormalD e fm sm --TE.sample pFlat SF.normal (flatMu :> flatten sigma :> TNil) --multiNormalD lpFlat (flatten mu) (flatten sigma)
        Cholesky cf ->
          let cM = TE.functionE SF.diagPostMultiply (cf :> flatten s :> TNil)
          in multiNormalC e fm cM
      modelCodeF (pE :> muE :> sigmaE :> TNil) rawE = do
        flatMu <- flattenCW (TE.declName nds <> "_mu") (TE.decl nds) muE
        case cent of
          Centered -> do
            unFlattenACW (TE.decl nds) rawE pE
            TE.addStmt $ sampleF rawE flatMu sigmaE
          NonCentered -> do
            ncfE <- nonCenteredFlat (TE.declName nds) (TE.decl nds) flatMu sigmaE rawE
            unFlattenACW (TE.decl nds) rawE pE

            let zeroMu =

  _ <- DAG.addBuildParameter $ DAG.TransformedP rawNDS [] TNil DAG.ModelBlockLocal justDeclare (DAG.build p :> muP :> sigmaP :> TNil) modelCodeF
  pure $ DAG.parameterTagExpr p
-}
