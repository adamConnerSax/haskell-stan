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
import qualified Stan.ModelBuilder.TypedExpressions.Operations as TE
import qualified Stan.ModelBuilder.TypedExpressions.StanFunctions as SF
import qualified Stan.ModelBuilder.TypedExpressions.DAGTypes as DAG
import qualified Stan.ModelBuilder.TypedExpressions.DAG as DAG
import qualified Stan.ModelBuilder as SB
import qualified Stan.ModelBuilder.BuildingBlocks.ArrayHelpers as SBBA

import qualified Data.Vec.Lazy as Vec
import qualified Data.Type.Nat as DT

import Prelude hiding (sum, All)

-- rows x cols matrix of parameters. Perhaps w Cholesky factor.
data MatrixCovarianceStructure = Diagonal | Cholesky (DAG.Parameter TE.ESqMat)

data Centering = Centered | NonCentered

type ParamC t = (TE.TypeOneOf t [TE.EMat, TE.EArray1 TE.EMat], TE.GenSType t)
type FParamC t = (TE.TypeOneOf t [TE.ECVec, TE.EArray1 TE.ECVec], TE.GenSType t)

type family FlatParamT t = ft | ft -> t where
  FlatParamT TE.EMat = TE.ECVec
  FlatParamT (TE.EArray (DT.S n) TE.EMat) = TE.EArray (DT.S n) TE.ECVec

makeVecArraySpec :: (DT.SNatI (DT.S m)
                    , forall f. TE.VecToTListC f m
                    , forall f. TE.TListToVecC f m
                    , TL.GenTypeList (TL.SameTypeList TE.EInt m)
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
        _ -> error "flatDS: Given array type of something other than matrices!"
    _ -> error "flatDS: Given type of something other than matrix or array of matrices!"

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
    _ -> error "flattenCW: Given type of something other than matrix or array of matrices!"

makeMatArraySpec :: (DT.SNatI (DT.S m)
                    , forall f. TE.VecToTListC f m
                    , forall f. TE.TListToVecC f m
                    , TL.GenTypeList (TL.SameTypeList TE.EInt m)
                    )
                 => [TE.VarModifier TE.UExpr (TE.ScalarType TE.EReal)]
                 -> Vec.Vec (DT.S m) TE.IntE
                 -> TE.IntE
                 -> TE.IntE
                 -> TE.DeclSpec (TE.EArray (DT.S m) TE.EMat)
makeMatArraySpec vms aDims rowsE colsE = TE.arraySpec DT.snat aDims $ TE.matrixSpec rowsE colsE vms

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


unFlattenACW :: TE.DeclSpec t -> TE.UExpr (FlatParamT t) -> TE.UExpr t -> TE.CodeWriter ()
unFlattenACW ds fe e = do
  let unFlatten x rowsE colsE =  TE.functionE SF.vecToMatrix (x :> rowsE :> colsE :> TNil)
  case ds of
    TE.DeclSpec TE.StanMatrix (rowsE Vec.::: colsE Vec.::: Vec.VNil) _ -> TE.addStmt (e `TE.assign` unFlatten fe rowsE colsE)
    TE.ArraySpec DT.SS arrDims mds -> case mds of
      TE.DeclSpec TE.StanMatrix (rowsE Vec.::: colsE Vec.::: Vec.VNil) _ -> unFlattenLoop "k" rowsE colsE arrDims e fe
      _ -> error "unflattenCW: Given array type of something other than matrices!"
    _ -> error "unflattenCW: Given type of something other than matrix or array of matrices!"

{-
nonCenteredFlat :: TE.StanName
                -> TE.DeclSpec t
                -> TE.UExpr (FlatParamT t)
                -> TE.MatrixE
                -> TE.UExpr (FlatParamT t)
                -> TE.CodeWriter (TE.UExpr (FlatParamT t))
nonCenteredFlat givenName ds flatMu sigmaE rawFlatE = do
  let --qfd m v = TE.functionE SF.quadFormDiag (m :> v :> TNil)
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
      _ -> error "nonCenteredFlat: Given array type of something other than matrices!"
    _ -> error "nonCenteredFlat: Given type of something other than matrix or array of matrices!"
-}

nonCenteredUnFlat :: TE.DeclSpec t
                  -> TE.UExpr t
                  -> TE.UExpr (FlatParamT t)
                  -> TE.MatrixE
                  -> TE.UExpr (FlatParamT t)
                  -> TE.CodeWriter ()
nonCenteredUnFlat ds pE flatMu sigmaE rawFlatE = do
  let --qfd m v = TE.functionE SF.quadFormDiag (m :> v :> TNil)
      flatten m = TE.functionE SF.to_vector (m :> TNil) -- column major
      unFlatten x rowsE colsE =  TE.functionE SF.vecToMatrix (x :> rowsE :> colsE :> TNil)
      flatSigma = flatten sigmaE
      eltMultiply = TE.binaryOpE (TE.SElementWise TE.SMultiply)
      ncufF :: TE.IntE -> TE.IntE -> TE.ExprList '[TE.ECVec, TE.ECVec] -> TE.MatrixE
      ncufF rowsE colsE (muFlat :> rawFlat :> TNil) = unFlatten (muFlat `TE.plusE` (rawFlat `eltMultiply` flatSigma)) rowsE colsE
  case ds of
    TE.DeclSpec TE.StanMatrix (rowsE Vec.::: colsE Vec.::: Vec.VNil) _
      -> TE.addStmt $ pE `TE.assign` ncufF rowsE colsE (flatMu :> rawFlatE :> TNil)
    TE.ArraySpec DT.SS arrDims mds -> case mds of
      TE.DeclSpec TE.StanMatrix (rowsE Vec.::: colsE Vec.::: Vec.VNil) _ -> do
--        ncfE <- TE.declareNW $ TE.NamedDeclSpec (givenName <> "_ncf") $ flatDS ds
        SBBA.applyToArrayOf' "k" (ncufF rowsE colsE) arrDims (SBBA.ArrayOf flatMu :> SBBA.ArrayOf rawFlatE :> TNil) pE
      _ -> error "nonCenteredFlat: Given array type of something other than matrices!"
    _ -> error "nonCenteredFlat: Given type of something other than matrix or array of matrices!"

zeroVec :: TE.IntE -> TE.VectorE
zeroVec lE = TE.functionE SF.rep_vector(TE.realE 0 :> lE :> TNil)

arrayOfZeroVecs :: (TL.VecToSameTypedListF TE.UExpr TE.EInt n
                   , TL.GenTypeList (TL.SameTypeList TE.EInt n)
                   , DT.SNatI n)
                => Vec.Vec (DT.S n) TE.IntE -> TE.IntE -> TE.UExpr (TE.EArray (DT.S n) TE.ECVec)
arrayOfZeroVecs arrDims lE = TE.functionE SF.rep_array (zeroVec lE :> TL.vecToSameTypedList arrDims)

zeroVecE :: TE.StanName -> TE.DeclSpec t -> TE.CodeWriter (TE.UExpr t)
zeroVecE name ds =
  TE.declareRHSNW (TE.NamedDeclSpec (name <> "_zero") ds)
  $ case ds of
      TE.DeclSpec TE.StanVector (lE Vec.::: Vec.VNil) _ -> zeroVec lE
      TE.ArraySpec DT.SS arrDims mds ->
        case mds of
          TE.DeclSpec TE.StanVector (lE Vec.::: Vec.VNil) _ -> arrayOfZeroVecs arrDims lE
          _ -> error "zeroVecE: Given array type of something other than vectors!"
      _ -> error "zeroVecE: Given type of something other than vector or array of vectors!"

stdNormalSigmaE :: TE.DeclSpec t -> TE.UExpr TE.ESqMat
stdNormalSigmaE ds =
  let sigmaE l = TE.functionE SF.diag (TE.functionE SF.rep_vector (TE.realE 1 :> l :> TNil) :> TNil)
  in   case ds of
    TE.DeclSpec TE.StanVector (lE Vec.::: Vec.VNil) _ -> sigmaE lE
    TE.ArraySpec DT.SS _ vds -> case vds of
      TE.DeclSpec TE.StanVector (lE Vec.::: Vec.VNil) _ -> sigmaE lE
      _ -> error "stdNormalSigmaE: Given array type of something other than vectors!"
    _ -> error "stdNormalSigmaE: Given type of something other than vector or array of vectors!"

stdNormalRaw ::  SF.MultiNormalDensityC t
             => MatrixCovarianceStructure -> TE.DeclSpec t -> TE.UExpr t -> TE.UExpr t -> TE.UStmt
stdNormalRaw cs ds zeroE rawFlatE = do
  case cs of
    Diagonal -> TE.sample rawFlatE SF.multi_normal (zeroE :> stdNormalSigmaE ds :> TNil)
    Cholesky cf -> TE.sample rawFlatE SF.multi_normal_cholesky (zeroE :> DAG.parameterExpr cf :> TNil)

matrixMultiNormalParameter :: forall t md gq .
                              (ParamC t
                              ,SF.MultiNormalDensityC (FlatParamT t)
                              )
                           => MatrixCovarianceStructure
                           -> Centering
                           -> DAG.Parameter t
                           -> DAG.Parameter TE.EMat
                           -> TE.NamedDeclSpec t
                           -> SB.StanBuilderM md gq (DAG.Parameter t)
matrixMultiNormalParameter cs cent muP sigmaP nds = do
  let flatten m = TE.functionE SF.to_vector (m :> TNil) -- column major
      multiNormalC x muFlat lSigma = TE.sample x SF.multi_normal_cholesky (muFlat :> lSigma :> TNil)
      multiNormalD x muFlat dSigma = TE.sample x SF.multi_normal (muFlat :> dSigma :> TNil)
      ds = TE.decl nds
      fDS = flatDS ds
      givenName = TE.declName nds
      justDeclare _ = DAG.DeclCodeF $ const $ pure ()
      noPriorCode _ _ = pure ()

  zeroE <- case cent of
    NonCentered -> SB.inBlock SB.SBTransformedData $ SB.addFromCodeWriter $ zeroVecE givenName fDS
    Centered -> pure $ TE.namedE "ERROR" $ TE.genSType @(FlatParamT t)
  pTag <- DAG.addBuildParameter $ DAG.TransformedP nds [] TNil DAG.ModelBlock justDeclare TNil noPriorCode
  let rawNDS = TE.NamedDeclSpec (TE.declName nds <> "_raw") fDS
      sampleF e fm s = case cs of
        Diagonal ->
          let sm = TE.functionE SF.diag (flatten s :> TNil)
          in multiNormalD e fm sm --TE.sample pFlat SF.normal (flatMu :> flatten sigma :> TNil) --multiNormalD lpFlat (flatten mu) (flatten sigma)
        Cholesky cfP ->
          let cM = TE.functionE SF.diagPostMultiply (DAG.parameterExpr cfP :> flatten s :> TNil)
          in multiNormalC e fm cM
      modelCodeF (pE :> muE :> sigmaE :> TNil) rawE = do
        flatMu <- flattenCW (TE.declName nds <> "_mu") (TE.decl nds) muE
        case cent of
          Centered -> do
            unFlattenACW (TE.decl nds) rawE pE
            TE.addStmt $ sampleF rawE flatMu sigmaE
          NonCentered -> do
            nonCenteredUnFlat (TE.decl nds) pE flatMu sigmaE rawE
            TE.addStmt $ stdNormalRaw cs fDS zeroE rawE
  _ <- DAG.addBuildParameter $ DAG.TransformedP rawNDS [] TNil DAG.ModelBlockLocal justDeclare (DAG.build pTag :> muP :> sigmaP :> TNil) modelCodeF
  pure $ DAG.build pTag

nonCentered :: TE.DeclSpec t
              -> TE.UExpr t
              -> TE.UExpr t
              -> TE.VectorE
              -> TE.UExpr t
              -> TE.CodeWriter ()
nonCentered ds ncE muE sigmaE rawE = do
  let --qfd m v = TE.functionE SF.quadFormDiag (m :> v :> TNil)
      eltMultiply = TE.binaryOpE (TE.SElementWise TE.SMultiply)
      ncF :: TE.ExprList '[TE.ECVec, TE.ECVec] -> TE.VectorE
      ncF (mu :> raw :> TNil) = mu `TE.plusE` (raw `eltMultiply` sigmaE)
  case ds of
    TE.DeclSpec TE.StanVector _ _ -> TE.addStmt $ ncE `TE.assign` ncF (muE :> rawE :> TNil)
    TE.ArraySpec DT.SS arrDims mds -> case mds of
      TE.DeclSpec TE.StanVector _ _ -> do
        SBBA.applyToArrayOf' "k" ncF arrDims (SBBA.ArrayOf muE :> SBBA.ArrayOf rawE :> TNil) ncE
      _ -> error "nonCentered: Given array type of something other than vectors!"
    _ -> error "nonCentered: Given type of something other than vector or array of vectors!"


-- given already declared parameters for mu (vector or array of vectors) and sigma (vector)
-- as well as cholesky factor if necessary
-- declares the given named parameter (vector or array of vectors) and models it with either
-- diagonal or cholesky multi-normal draws, using either the centered or non-centered parameterization.
-- In the non-centered case, declares another parameter for the standard normal draws
-- and then assigns the declared one appropriately. That part is locally scoped in the model block.
vectorMultiNormalParameter :: (SF.MultiNormalDensityC t)
                           => MatrixCovarianceStructure
                           -> Centering
                           -> DAG.Parameter t
                           -> DAG.Parameter TE.ECVec
                           -> TE.NamedDeclSpec t
                           -> SB.StanBuilderM md gq (DAG.Parameter t)
vectorMultiNormalParameter cs cent muP sigmaP nds = do
  let multiNormalC x mu lSigma = TE.sample x SF.multi_normal_cholesky (mu :> lSigma :> TNil)
      multiNormalD x mu dSigma = TE.sample x SF.multi_normal (mu :> dSigma :> TNil)
      ds = TE.decl nds
      givenName = TE.declName nds
      noPriorCode _ _ = pure ()
      justDeclare _ = DAG.DeclCodeF $ const $ pure ()
  let sampleF e m s = case cs of
        Diagonal ->
          let sm = TE.functionE SF.diag (s :> TNil)
          in multiNormalD e m sm
        Cholesky cf ->
          let cM = TE.functionE SF.diagPostMultiply (DAG.parameterExpr cf :> s :> TNil)
          in multiNormalC e m cM
  case cent of
    Centered -> do
      let sampleCW (m :> s :> TNil) e = TE.addStmt $ sampleF e m s
      fmap DAG.build
        $ DAG.addBuildParameter
        $ DAG.TransformedP nds [] TNil DAG.ModelBlock justDeclare (muP :> sigmaP :> TNil) sampleCW
    NonCentered -> do
      zeroE <- SB.inBlock SB.SBTransformedData $ SB.addFromCodeWriter $ zeroVecE givenName ds
      ncPTag <- DAG.addBuildParameter $ DAG.TransformedP nds [] TNil DAG.ModelBlock justDeclare TNil noPriorCode
      let rawNDS = TE.NamedDeclSpec (TE.declName nds <> "_raw") ds
          cPList = DAG.build ncPTag :> muP :> sigmaP :> TNil
          cCode (ncE :> muE :> sigmaE :> TNil) rawE = do
            TE.addStmt $ stdNormalRaw cs ds zeroE rawE
            nonCentered ds ncE muE sigmaE rawE
      _ <- DAG.addBuildParameter $ DAG.TransformedP rawNDS [] TNil DAG.ModelBlockLocal justDeclare cPList cCode
      pure $ DAG.build ncPTag

{-
unFlatDS :: forall t . TE.DeclSpec t -> TE.DeclSpec t
unFlatDS ds =
  case ds of
    TE.DeclSpec TE.StanMatrix (rowsE Vec.::: colsE Vec.::: Vec.VNil) vms -> TE.matrixSpec rowsE colsE vms
    TE.ArraySpec n@DT.SS arrDims mds ->
      case mds of
        TE.DeclSpec TE.StanMatrix (rowsE Vec.::: colsE Vec.::: Vec.VNil) vms ->
          DT.withSNat n $ makeMatArraySpec vms arrDims rowsE colsE
    _ -> error "flatDS: Given type of something other than matrix or array of matrices!"


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
-}
