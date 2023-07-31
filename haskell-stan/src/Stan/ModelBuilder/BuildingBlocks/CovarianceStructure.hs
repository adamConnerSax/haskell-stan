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

flattenACW :: (ParamC t)
          => TE.DeclSpec t -> TE.UExpr t -> TE.UExpr (FlatParamT t) ->  TE.CodeWriter ()
flattenACW ds e eFlat =
  let flatten x =  TE.functionE SF.to_vector (x :> TNil)
  in case ds of
    TE.DeclSpec TE.StanMatrix _ _ -> TE.addStmt $ eFlat `TE.assign` flatten e
    TE.ArraySpec DT.SS arrDims mds -> do
      case mds of
        TE.DeclSpec TE.StanMatrix _ _ -> flattenLoop "k" arrDims eFlat e
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
      _ -> error "unflattenACW: Given array type of something other than matrices!"
    _ -> error "unflattenACW: Given type of something other than matrix or array of matrices!"

{-
nonCenteredFlat' :: TE.DeclSpec t
                 -> TE.UExpr (FlatParamT t)
                 -> TE.MatrixE
                 -> TE.UExpr (FlatParamT t)
                 -> TE.UExpr t
                 -> TE.CodeWriter ()
nonCenteredFlat' givenName ds flatMu sigmaE rawFlatE e = do
  let --qfd m v = TE.functionE SF.quadFormDiag (m :> v :> TNil)
      flatten m = TE.functionE SF.to_vector (m :> TNil) -- column major
      flatSigma = flatten sigmaE
      eltMultiply = TE.binaryOpE (TE.SElementWise TE.SMultiply)
      ncfF :: TE.ExprList '[TE.ECVec, TE.ECVec] -> TE.VectorE
      ncfF (muFlat :> rawFlat :> TNil) = muFlat `TE.plusE` (rawFlat `eltMultiply` flatSigma)
  case ds of
    TE.DeclSpec TE.StanMatrix _ _ -> TE.addStmt $ pure $ ncfF (flatMu :> rawFlatE :> TNil)
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

stdNormalSigmaE :: TE.StanName -> TE.DeclSpec t -> TE.CodeWriter (TE.UExpr TE.ESqMat)
stdNormalSigmaE n ds =
  let sigmaE l = TE.functionE SF.diag_matrix (TE.functionE SF.rep_vector (TE.realE 1 :> l :> TNil) :> TNil)
      nds l = TE.NamedDeclSpec (n <> "_diag1") $ TE.sqMatrixSpec l []
  in case ds of
    TE.DeclSpec TE.StanVector (lE Vec.::: Vec.VNil) _ -> TE.declareRHSNW (nds lE) $ sigmaE lE
    TE.ArraySpec DT.SS _ vds -> case vds of
      TE.DeclSpec TE.StanVector (lE Vec.::: Vec.VNil) _ -> TE.declareRHSNW (nds lE) $ sigmaE lE
      _ -> error "stdNormalSigmaE: Given array type of something other than vectors!"
    _ -> error "stdNormalSigmaE: Given type of something other than vector or array of vectors!"

--stdNormalSigmaE ::

stdNormalRaw ::  SF.MultiNormalDensityC t
             => MatrixCovarianceStructure -> TE.UExpr t -> TE.SqMatrixE -> TE.UExpr t -> TE.UStmt
stdNormalRaw cs zeroE diag1E rawFlatE = do
  case cs of
    Diagonal -> TE.sample rawFlatE SF.multi_normal (zeroE :> diag1E :> TNil)
    Cholesky cf -> TE.sample rawFlatE SF.multi_normal_cholesky (zeroE :> DAG.parameterExpr cf :> TNil)

matrixMultiNormalParameter :: forall t md gq .
                              (ParamC t
                              ,SF.MultiNormalDensityC (FlatParamT t)
                              )
                           => MatrixCovarianceStructure
                           -> Centering
                           -> DAG.Parameter t
                           -> DAG.Parameter TE.EMat --TE.MatrixE
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
      flatSigmaP = DAG.mapped flatten sigmaP
  zeroE <- case cent of
    NonCentered -> SB.inBlock SB.SBTransformedData $ SB.addFromCodeWriter $ zeroVecE givenName fDS
    Centered -> pure $ TE.namedE "ERROR" $ TE.genSType @(FlatParamT t)
--  pTag <- DAG.addBuildParameter $ DAG.TransformedP nds [] TNil DAG.ModelBlock justDeclare TNil noPriorCode
  p <- DAG.addBuildParameter $ DAG.UntransformedP nds [] TNil noPriorCode
  let rawNDS = TE.NamedDeclSpec (TE.declName nds <> "_raw") fDS
      sampleF e fm s = case cs of
        Diagonal ->
          let sm = TE.functionE SF.diag_matrix (s :> TNil)
          in multiNormalD e fm sm --TE.sample pFlat SF.normal (flatMu :> flatten sigma :> TNil) --multiNormalD lpFlat (flatten mu) (flatten sigma)
        Cholesky cfP ->
          let cM = TE.functionE SF.diagPostMultiply (DAG.parameterExpr cfP :> s :> TNil)
          in multiNormalC e fm cM
  case cent of
    Centered -> do
      let modelCodeF (pE :> muE' :> sigmaE' :> TNil) rawE = do
            flatMu <- flattenCW (TE.declName nds <> "_flatMu") (TE.decl nds) muE'
            flattenACW (TE.decl nds) pE rawE
            TE.addStmt $ sampleF rawE flatMu sigmaE'
      _ <- DAG.addBuildParameter $ DAG.TransformedP rawNDS [] TNil DAG.ModelBlockLocal justDeclare (p :> muP :> flatSigmaP :> TNil) modelCodeF
      pure p
    NonCentered -> SB.stanBuildError "Unsupported"
{-
      flatMuP <- DAG.build
                 $ DAG.addBuildParameter
                 $ DAG.TransformedP
                 (TE.NamedDeclSpec (TE.declName nds <> "_flatMu") fDS) []
                 (muP :> TNil) DAG.TransformedParametersBlock
                 (\(muE :> TNil) -> DAG.DeclCode $ \flatMuE -> flattenACW ds muE flatMuE)
                 TNil noPriorCode
      mnVecP <- vectorMultiNormalParameter cs cent flatMuP flatSigmaP fDS
      fmap DAG.build
        $ DAG.addBuildParameter
        $ DAG.TransformedP nds []
        (mnVecP :> TNil) DAG.TransformedParametersBlock
        (vec)

      let modelCodeF (pE :> muE' :> sigmaE' :> TNil) rawE = do
            flatMu <- flattenCW (TE.declName nds <> "_flatMu") (TE.decl nds) muE'
            TE.addStmt $ stdNormalRaw cs fDS zeroE rawE

            nonCenteredUnFlat (TE.decl nds) pE flatMu sigmaE' rawE
      _ <- DAG.addBuildParameter $ DAG.TransformedP rawNDS [] TNil DAG.ModelBlockLocal justDeclare (DAG.build pTag :> muP :> sigmaP :> TNil) modelCodeF
-}

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
  let sampleF e m s = case cs of
        Diagonal ->
          let sm = TE.functionE SF.diag_matrix (s :> TNil)
          in multiNormalD e m sm
        Cholesky cf ->
          let cM = TE.functionE SF.diagPostMultiply (DAG.parameterExpr cf :> s :> TNil)
          in multiNormalC e m cM
  case cent of
    Centered -> do
      let sampleCW (m :> s :> TNil) e = TE.addStmt $ sampleF e m s
      DAG.addBuildParameter
        $ DAG.UntransformedP nds [] (muP :> sigmaP :> TNil) sampleCW
    NonCentered -> do
      let rawNDS = TE.NamedDeclSpec (TE.declName nds <> "_raw") ds
      (zeroE, diag1E) <- SB.inBlock SB.SBTransformedData
                         $ SB.addFromCodeWriter
                         $ (do
                               zv <- zeroVecE givenName ds
                               d1 <- stdNormalSigmaE givenName ds
                               pure (zv, d1)
                           )
      rawP <- DAG.addBuildParameter $ DAG.UntransformedP rawNDS []
              TNil
              (\_ rawE -> TE.addStmt $ stdNormalRaw cs zeroE diag1E rawE)
      let  cDeclCode (rawE :> muE :> sigmaE :> TNil) =
            DAG.DeclCodeF $ \ncE -> nonCentered ds ncE muE sigmaE rawE
      DAG.addBuildParameter
        $ DAG.TransformedP nds []
        (rawP :> muP :> sigmaP :> TNil)
        DAG.TransformedParametersBlock
        cDeclCode
        TNil (\_ _ -> pure ())


matrixMultiNormalParameter' :: forall t md gq .
                              (ParamC t
                              ,SF.MultiNormalDensityC (FlatParamT t)
                              )
                            => MatrixCovarianceStructure
                            -> Centering
                            -> DAG.Parameter t
                            -> DAG.Parameter TE.EMat
                            -> TE.NamedDeclSpec t
                            -> SB.StanBuilderM md gq (DAG.Parameter t)
matrixMultiNormalParameter' cs cent muP sigmaP nds = do
  let n =  TE.declName nds
      ds = TE.decl nds
      fDS = flatDS ds
      flatten x =  TE.functionE SF.to_vector (x :> TNil)
      flatSigmaP = DAG.mapped flatten sigmaP
      vName = n <> "V"
      ndsV = TE.NamedDeclSpec vName fDS
  flatMuP <- DAG.addBuildParameter
             $ DAG.TransformedP
             (TE.NamedDeclSpec (n <> "_flatMu") fDS) []
             (muP :> TNil)
             DAG.TransformedParametersBlock
             (\(muE :> TNil) -> DAG.DeclCodeF $ \flatMuE -> flattenACW ds muE flatMuE)
             TNil
             (\_ _ -> pure ())
  vecP <- vectorMultiNormalParameter cs cent flatMuP flatSigmaP ndsV
  DAG.addBuildParameter
    $ DAG.TransformedP
    nds []
    (vecP :> TNil)
    DAG.TransformedParametersBlock
    (\(vecE :> TNil) -> DAG.DeclCodeF $ \matE -> unFlattenACW ds vecE matE)
    TNil
    (\_ _ -> pure ())
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
