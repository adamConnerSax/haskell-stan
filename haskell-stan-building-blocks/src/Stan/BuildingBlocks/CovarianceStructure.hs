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
{-# LANGUAGE TypeFamilyDependencies #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use for_" #-}
{-# HLINT ignore "Use camelCase" #-}

module Stan.BuildingBlocks.CovarianceStructure
  (
    module Stan.BuildingBlocks.CovarianceStructure
  )
where

import Prelude hiding (Nat, sum, All)

import qualified Stan.Language as SL
import qualified Stan.Language.Statement as SL
import Stan.Language (TypedList(..))
import Stan.Language.Recursion (hfmap)
import qualified Stan.Functions as SF
import Stan.Functions.Operators
import qualified Stan.Builder as SB
import qualified Stan.BuildingBlocks.ArrayHelpers as SBBA
{-
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
-}

import qualified Data.Vec.Lazy as Vec
import qualified Data.Type.Nat as DT

import Effectful (Eff)
-- rows x cols matrix of parameters. Perhaps w Cholesky factor.
data MatrixCovarianceStructure = Diagonal | Cholesky (SB.Parameter SL.ESqMat)

data Centering = Centered | NonCentered

type ParamC t = (SL.TypeOneOf t [SL.EMat, SL.EArray1 SL.EMat], SL.GenSType t)
type FParamC t = (SL.TypeOneOf t [SL.ECVec, SL.EArray1 SL.ECVec], SL.GenSType t)

type family FlatParamT t = ft | ft -> t where
  FlatParamT SL.EMat = SL.ECVec
  FlatParamT (SL.EArray (DT.S n) SL.EMat) = SL.EArray (DT.S n) SL.ECVec

makeVecArraySpec :: (DT.SNatI (DT.S m)
                    , forall f. SL.VecToTListC f m
                    , forall f. SL.TListToVecC f m
                    , SL.GenSTypeList (SL.SameTypeList SL.EInt m)
                    )
                 => SL.VarModifiers SL.UExpr (SL.ScalarType SL.EReal)
                 -> Vec.Vec (DT.S m) SL.IntE
                 -> SL.IntE
                 -> SL.IntE
                 -> SL.DeclSpec SL.UExpr (SL.EArray (DT.S m) SL.ECVec)
makeVecArraySpec vms aDims rowsE colsE = SL.arraySpec DT.snat aDims $ SL.addVMs vms $ SL.vectorSpec (rowsE `SL.timesE`colsE)

flatDS :: forall t . SL.DeclSpec SL.UExpr t -> SL.DeclSpec SL.UExpr (FlatParamT t)
flatDS ds =
  case ds of
    SL.MatrixSpec SL.StanMatrix rowsE colsE vms ->
      SL.addVMs vms $ SL.vectorSpec (rowsE `SL.timesE` colsE)
    SL.ArraySpec n@DT.SS arrDims mds ->
      case mds of
        SL.MatrixSpec SL.StanMatrix rowsE colsE vms ->
          DT.withSNat n $ makeVecArraySpec vms arrDims rowsE colsE
        _ -> error "flatDS: Given array type of something other than matrices!"
    _ -> error "flatDS: Given type of something other than matrix or array of matrices!"

flattenLoop :: forall n .
               (SL.SameTypedListToVecF SL.UExpr SL.EInt n
               , SL.VecToSameTypedListF SL.VarAndForType SL.EInt n
               , DT.SNatI n
               )
            => Text
            -> Vec.Vec (DT.S n) SL.IntE
            -> SL.UExpr (SL.EArray (DT.S n) SL.ECVec)
            -> SL.UExpr (SL.EArray (DT.S n) SL.EMat)
            -> SL.CodeWriter ()
flattenLoop counterPrefix arrDims aVecE aMatE = SBBA.applyToArrayOf counterPrefix SF.to_vector arrDims aMatE aVecE

flattenCW :: (ParamC t)
          => SL.VarName -> SL.DeclSpec SL.UExpr t -> SL.UExpr t -> SL.CodeWriter (SL.UExpr (FlatParamT t))
flattenCW sn ds e =
  let flatten x =  SF.to_vector x
  in case ds of
    SL.MatrixSpec SL.StanMatrix _ _ _ -> pure $ flatten e
    SL.ArraySpec DT.SS arrDims mds -> do
      case mds of
        SL.MatrixSpec SL.StanMatrix _ _ _ -> do
          fv <- SL.declareNW $ SL.NamedDeclSpec (sn <> "_flat") $ flatDS ds
          flattenLoop "k" arrDims fv e
          pure fv
    _ -> error "flattenCW: Given type of something other than matrix or array of matrices!"

flattenACW :: (ParamC t)
          => SL.DeclSpec SL.UExpr t -> SL.UExpr t -> SL.UExpr (FlatParamT t) ->  SL.CodeWriter ()
flattenACW ds e eFlat =
  let flatten x =  SF.to_vector x
  in case ds of
    SL.MatrixSpec SL.StanMatrix _ _ _ -> SL.addStmt $ eFlat SL.|=| flatten e
    SL.ArraySpec DT.SS arrDims mds -> do
      case mds of
        SL.MatrixSpec SL.StanMatrix _ _ _ -> flattenLoop "k" arrDims eFlat e
    _ -> error "flattenCW: Given type of something other than matrix or array of matrices!"


makeMatArraySpec :: (DT.SNatI (DT.S m)
                    , forall f. SL.VecToTListC f m
                    , forall f. SL.TListToVecC f m
                    , SL.GenSTypeList (SL.SameTypeList SL.EInt m)
                    )
                 => SL.VarModifiers SL.UExpr (SL.ScalarType SL.EReal)
                 -> Vec.Vec (DT.S m) SL.IntE
                 -> SL.IntE
                 -> SL.IntE
                 -> SL.DeclSpec SL.UExpr (SL.EArray (DT.S m) SL.EMat)
makeMatArraySpec vms aDims rowsE colsE = SL.arraySpec DT.snat aDims $ SL.addVMs vms $ SL.matrixSpec rowsE colsE

unFlattenLoop :: forall n .
                 (SL.SameTypedListToVecF SL.UExpr SL.EInt n
                 , SL.VecToSameTypedListF SL.VarAndForType SL.EInt n
                 , DT.SNatI n
                 )
              => Text
              -> SL.IntE
              -> SL.IntE
              -> Vec.Vec (DT.S n) SL.IntE
              -> SL.UExpr (SL.EArray (DT.S n) SL.EMat)
              -> SL.UExpr (SL.EArray (DT.S n) SL.ECVec)
              -> SL.CodeWriter ()
unFlattenLoop counterPrefix rowsE colsE arrDims ufE fE =
  SBBA.applyToArrayOf counterPrefix (\x -> SF.vecToMatrix x rowsE colsE) arrDims fE ufE


unFlattenACW :: SL.DeclSpec SL.UExpr t -> SL.UExpr (FlatParamT t) -> SL.UExpr t -> SL.CodeWriter ()
unFlattenACW ds fe e = do
  let unFlatten x rowsE colsE = SF.vecToMatrix x rowsE colsE
  case ds of
    SL.MatrixSpec SL.StanMatrix rowsE colsE _ -> SL.addStmt (e SL.|=| unFlatten fe rowsE colsE)
    SL.ArraySpec DT.SS arrDims mds -> case mds of
      SL.MatrixSpec SL.StanMatrix rowsE colsE _ -> unFlattenLoop "k" rowsE colsE arrDims e fe
      _ -> error "unflattenACW: Given array type of something other than matrices!"
    _ -> error "unflattenACW: Given type of something other than matrix or array of matrices!"

{-
nonCenteredFlat' :: SL.DeclSpec t
                 -> SL.UExpr (FlatParamT t)
                 -> SL.MatrixE
                 -> SL.UExpr (FlatParamT t)
                 -> SL.UExpr t
                 -> SL.CodeWriter ()
nonCenteredFlat' givenName ds flatMu sigmaE rawFlatE e = do
  let --qfd m v = SL.functionE SF.quadFormDiag (m :> v :> TNil)
      flatten m = SL.functionE SF.to_vector (m :> TNil) -- column major
      flatSigma = flatten sigmaE
      eltMultiply = SL.binaryOpE (SL.SElementWise SL.SMultiply)
      ncfF :: SL.ExprList '[SL.ECVec, SL.ECVec] -> SL.VectorE
      ncfF (muFlat :> rawFlat :> TNil) = muFlat `SL.plusE` (rawFlat `eltMultiply` flatSigma)
  case ds of
    SL.DeclSpec SL.StanMatrix _ _ -> SL.addStmt $ pure $ ncfF (flatMu :> rawFlatE :> TNil)
    SL.ArraySpec DT.SS arrDims mds -> case mds of
      SL.DeclSpec SL.StanMatrix _ _ -> do
        ncfE <- SL.declareNW $ SL.NamedDeclSpec (givenName <> "_ncf") $ flatDS ds
        SBBA.applyToArrayOf' "k" ncfF arrDims (SBBA.ArrayOf flatMu :> SBBA.ArrayOf rawFlatE :> TNil) ncfE
        pure ncfE
      _ -> error "nonCenteredFlat: Given array type of something other than matrices!"
    _ -> error "nonCenteredFlat: Given type of something other than matrix or array of matrices!"
-}

nonCenteredUnFlat :: SL.DeclSpec SL.UExpr t
                  -> SL.UExpr t
                  -> SL.UExpr (FlatParamT t)
                  -> SL.MatrixE
                  -> SL.UExpr (FlatParamT t)
                  -> SL.CodeWriter ()
nonCenteredUnFlat ds pE flatMu sigmaE rawFlatE = do
  let --qfd m v = SL.functionE SF.quadFormDiag (m :> v :> TNil)
      flatten m = SF.to_vector m -- column major
      unFlatten x rowsE colsE =  SF.vecToMatrix x rowsE colsE
      flatSigma = flatten sigmaE
      eltMultiply = SL.binaryOpE (SL.SElementWise SL.SMultiply)
      ncufF :: SL.IntE -> SL.IntE -> SL.ExprList '[SL.ECVec, SL.ECVec] -> SL.MatrixE
      ncufF rowsE colsE (muFlat :> rawFlat :> TNil) = unFlatten (muFlat `SL.plusE` (rawFlat `eltMultiply` flatSigma)) rowsE colsE
  case ds of
    SL.MatrixSpec SL.StanMatrix rowsE colsE  _
      -> SL.addStmt $ pE `SL.assign` ncufF rowsE colsE (flatMu :> rawFlatE :> TNil)
    SL.ArraySpec DT.SS arrDims mds -> case mds of
      SL.MatrixSpec SL.StanMatrix rowsE colsE _ -> do
--        ncfE <- SL.declareNW $ SL.NamedDeclSpec (givenName <> "_ncf") $ flatDS ds
        SBBA.applyToArrayOf' "k" (ncufF rowsE colsE) arrDims (SBBA.ArrayOf flatMu :> SBBA.ArrayOf rawFlatE :> TNil) pE
      _ -> error "nonCenteredFlat: Given array type of something other than matrices!"
    _ -> error "nonCenteredFlat: Given type of something other than matrix or array of matrices!"

zeroVec :: SL.IntE -> SL.VectorE
zeroVec lE = SF.rep_vector (SL.realE 0) lE

arrayOfZeroVecs :: (SL.VecToSameTypedListF SL.UExpr SL.EInt n
                   , SL.GenSTypeList (SL.SameTypeList SL.EInt n)
                   , DT.SNatI n)
                => Vec.Vec (DT.S n) SL.IntE -> SL.IntE -> SL.UExpr (SL.EArray (DT.S n) SL.ECVec)
arrayOfZeroVecs arrDims lE = SL.functionE SF.rep_array' (zeroVec lE :> SL.vecToSameTypedList arrDims)

zeroVecE :: SL.VarName -> SL.DeclSpec SL.UExpr t -> SL.CodeWriter (SL.UExpr t)
zeroVecE name ds =
  SL.declareRHSNW (SL.NamedDeclSpec (name <> "_zero") ds)
  $ case ds of
      SL.VectorSpec SL.StanVector lE _ -> zeroVec lE
      SL.ArraySpec DT.SS arrDims mds ->
        case mds of
          SL.VectorSpec SL.StanVector lE _ -> arrayOfZeroVecs arrDims lE
          _ -> error "zeroVecE: Given array type of something other than vectors!"
      _ -> error "zeroVecE: Given type of something other than vector or array of vectors!"

stdNormalSigmaE :: SL.VarName -> SL.DeclSpec SL.UExpr t -> SL.CodeWriter (SL.UExpr SL.ESqMat)
stdNormalSigmaE n ds =
  let sigmaE l = SF.diag_matrix (SF.rep_vector (SL.realE 1) l)
      nds l = SL.NamedDeclSpec (n <> "_diag1") $ SL.sqMatrixSpec l
  in case ds of
    SL.VectorSpec SL.StanVector lE _ -> SL.declareRHSNW (nds lE) $ sigmaE lE
    SL.ArraySpec DT.SS _ vds -> case vds of
      SL.VectorSpec SL.StanVector lE _ -> SL.declareRHSNW (nds lE) $ sigmaE lE
      _ -> error "stdNormalSigmaE: Given array type of something other than vectors!"
    _ -> error "stdNormalSigmaE: Given type of something other than vector or array of vectors!"

--stdNormalSigmaE ::

stdNormalRaw ::  SF.MultiNormalDensityC t
             => MatrixCovarianceStructure -> SL.UExpr t -> SL.SqMatrixE -> SL.UExpr t -> SL.UStmt
stdNormalRaw cs zeroE diag1E rawFlatE = do
  case cs of
    Diagonal -> SL.sample rawFlatE SF.multi_normal (zeroE :> diag1E :> TNil)
    Cholesky cf -> SL.sample rawFlatE SF.multi_normal_cholesky (zeroE :> SB.parameterExpr cf :> TNil)

matrixMultiNormalParameter :: forall t es .
                              (ParamC t
                              ,SF.MultiNormalDensityC (FlatParamT t)
                              , SB.StanParametersC es
                              , SB.StanCodeC es
                              )
                           => MatrixCovarianceStructure
                           -> Centering
                           -> SB.Parameter t
                           -> SB.Parameter SL.EMat --SL.MatrixE
                           -> SL.NamedDeclSpec t
                           -> Eff es (SB.Parameter t)
matrixMultiNormalParameter cs cent muP sigmaP nds = do
  let flatten m = SF.to_vector m  -- column major
      multiNormalC x muFlat lSigma = SL.sample x SF.multi_normal_cholesky (muFlat :> lSigma :> TNil)
      multiNormalD x muFlat dSigma = SL.sample x SF.multi_normal (muFlat :> dSigma :> TNil)
      ds = SL.decl nds
      fDS = flatDS ds
      givenName = SL.declName nds
      justDeclare _ = SB.DeclCodeF $ const $ pure ()
      noPriorCode _ _ = pure ()
      flatSigmaP = SB.mapped flatten sigmaP
  zeroE <- case cent of
    NonCentered -> SB.inBlock SL.SBTransformedData $ SB.addFromCodeWriter $ zeroVecE givenName fDS
    Centered -> pure $ SL.namedE "ERROR" $ SL.genSType @(FlatParamT t)
--  pTag <- DAG.addBuildParameter $ DAG.TransformedP nds [] TNil DAG.ModelBlock justDeclare TNil noPriorCode
  p <- SB.addBuildParameter $ SB.UntransformedP nds [] TNil noPriorCode
  let rawNDS = SL.NamedDeclSpec (SL.declName nds <> "_raw") fDS
      sampleF e fm s = case cs of
        Diagonal ->
          let sm = SF.diag_matrix s
          in multiNormalD e fm sm --SL.sample pFlat SF.normal (flatMu :> flatten sigma :> TNil) --multiNormalD lpFlat (flatten mu) (flatten sigma)
        Cholesky cfP ->
          let cM = SF.diag_post_multiply (SB.parameterExpr cfP) s
          in multiNormalC e fm cM
  case cent of
    Centered -> do
      let modelCodeF (pE :> muE' :> sigmaE' :> TNil) rawE = do
            flatMu <- flattenCW (SL.declName nds <> "_flatMu") (SL.decl nds) muE'
            flattenACW (SL.decl nds) pE rawE
            SL.addStmt $ sampleF rawE flatMu sigmaE'
      _ <- SB.addBuildParameter $ SB.TransformedP rawNDS [] TNil SB.ModelBlockLocal justDeclare (p :> muP :> flatSigmaP :> TNil) modelCodeF
      pure p
    NonCentered -> SB.buildError "matrixMultiNormalParameter: Unsupported Non-Centered structure"
{-
      flatMuP <- DAG.build
                 $ DAG.addBuildParameter
                 $ DAG.TransformedP
                 (SL.NamedDeclSpec (SL.declName nds <> "_flatMu") fDS) []
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
            flatMu <- flattenCW (SL.declName nds <> "_flatMu") (SL.decl nds) muE'
            SL.addStmt $ stdNormalRaw cs fDS zeroE rawE

            nonCenteredUnFlat (SL.decl nds) pE flatMu sigmaE' rawE
      _ <- DAG.addBuildParameter $ DAG.TransformedP rawNDS [] TNil DAG.ModelBlockLocal justDeclare (DAG.build pTag :> muP :> sigmaP :> TNil) modelCodeF
-}

nonCentered :: SL.DeclSpec SL.UExpr t
              -> SL.UExpr t
              -> SL.UExpr t
              -> SL.VectorE
              -> SL.UExpr t
              -> SL.CodeWriter ()
nonCentered ds ncE muE sigmaE rawE = do
  let --qfd m v = SL.functionE SF.quadFormDiag (m :> v :> TNil)
      eltMultiply = SL.binaryOpE (SL.SElementWise SL.SMultiply)
      ncF :: SL.ExprList '[SL.ECVec, SL.ECVec] -> SL.VectorE
      ncF (mu :> raw :> TNil) = mu |+| (raw |.*| sigmaE)
  case ds of
    SL.VectorSpec SL.StanVector _ _ -> SL.addStmt $ ncE SL.|=| ncF (muE :> rawE :> TNil)
    SL.ArraySpec DT.SS arrDims mds -> case mds of
      SL.VectorSpec SL.StanVector _ _ -> do
        SBBA.applyToArrayOf' "k" ncF arrDims (SBBA.ArrayOf muE :> SBBA.ArrayOf rawE :> TNil) ncE
      _ -> error "nonCentered: Given array type of something other than vectors!"
    _ -> error "nonCentered: Given type of something other than vector or array of vectors!"


-- given already declared parameters for mu (vector or array of vectors) and sigma (vector)
-- as well as cholesky factor if necessary
-- declares the given named parameter (vector or array of vectors) and models it with either
-- diagonal or cholesky multi-normal draws, using either the centered or non-centered parameterization.
-- In the non-centered case, declares another parameter for the standard normal draws
-- and then assigns the declared one appropriately. That part is locally scoped in the model block.
vectorMultiNormalParameter :: (SF.MultiNormalDensityC t
                              , SB.StanParametersC es
                              , SB.StanCodeC es
                              )
                           => MatrixCovarianceStructure
                           -> Centering
                           -> SB.Parameter t
                           -> SB.Parameter SL.ECVec
                           -> SL.NamedDeclSpec t
                           -> Eff es (SB.Parameter t)
vectorMultiNormalParameter cs cent muP sigmaP nds = do
  let multiNormalC x mu lSigma = SL.sample x SF.multi_normal_cholesky (mu :> lSigma :> TNil)
      multiNormalD x mu dSigma = SL.sample x SF.multi_normal (mu :> dSigma :> TNil)
      ds = SL.decl nds
      givenName = SL.declName nds
  let sampleF e m s = case cs of
        Diagonal ->
          let sm = SF.diag_matrix s
          in multiNormalD e m sm
        Cholesky cf ->
          let cM = SF.diag_post_multiply (SB.parameterExpr cf) s
          in multiNormalC e m cM
  case cent of
    Centered -> do
      let sampleCW (m :> s :> TNil) e = SL.addStmt $ sampleF e m s
      SB.addBuildParameter
        $ SB.UntransformedP nds [] (muP :> sigmaP :> TNil) sampleCW
    NonCentered -> do
      let rawNDS = SL.NamedDeclSpec (SL.declName nds <> "_raw") ds
      (zeroE, diag1E) <- SB.inBlock SL.SBTransformedData
                         $ SB.addFromCodeWriter
                         $ (do
                               zv <- zeroVecE givenName ds
                               d1 <- stdNormalSigmaE givenName ds
                               pure (zv, d1)
                           )
      rawP <- SB.addBuildParameter $ SB.UntransformedP rawNDS []
              TNil
              (\_ rawE -> SL.addStmt $ stdNormalRaw cs zeroE diag1E rawE)
      let  cDeclCode (rawE :> muE :> sigmaE :> TNil) =
            SB.DeclCodeF $ \ncE -> nonCentered ds ncE muE sigmaE rawE
      SB.addBuildParameter
        $ SB.TransformedP nds []
        (rawP :> muP :> sigmaP :> TNil)
        SB.TransformedParametersBlock
        cDeclCode
        TNil (\_ _ -> pure ())


matrixMultiNormalParameter' :: forall t es .
                              (ParamC t
                              ,SF.MultiNormalDensityC (FlatParamT t)
                              , SB.StanParametersC es
                              , SB.StanCodeC es
                              )
                            => MatrixCovarianceStructure
                            -> Centering
                            -> SB.Parameter t
                            -> SB.Parameter SL.EMat
                            -> SL.NamedDeclSpec t
                            -> Eff es (SB.Parameter t)
matrixMultiNormalParameter' cs cent muP sigmaP nds = do
  let n =  SL.declName nds
      ds = SL.decl nds
      fDS = flatDS ds
      flatten x =  SF.to_vector x
      flatSigmaP = SB.mapped flatten sigmaP
      vName = n <> "V"
      ndsV = SL.NamedDeclSpec vName fDS
  flatMuP <- SB.addBuildParameter
             $ SB.TransformedP
             (SL.NamedDeclSpec (n <> "_flatMu") fDS) []
             (muP :> TNil)
             SB.TransformedParametersBlock
             (\(muE :> TNil) -> SB.DeclCodeF $ \flatMuE -> flattenACW ds muE flatMuE)
             TNil
             (\_ _ -> pure ())
  vecP <- vectorMultiNormalParameter cs cent flatMuP flatSigmaP ndsV
  SB.addBuildParameter
    $ SB.TransformedP
    nds []
    (vecP :> TNil)
    SB.TransformedParametersBlock
    (\(vecE :> TNil) -> SB.DeclCodeF $ \matE -> unFlattenACW ds vecE matE)
    TNil
    (\_ _ -> pure ())
{-
unFlatDS :: forall t . SL.DeclSpec t -> SL.DeclSpec t
unFlatDS ds =
  case ds of
    SL.DeclSpec SL.StanMatrix (rowsE Vec.::: colsE Vec.::: Vec.VNil) vms -> SL.matrixSpec rowsE colsE vms
    SL.ArraySpec n@DT.SS arrDims mds ->
      case mds of
        SL.DeclSpec SL.StanMatrix (rowsE Vec.::: colsE Vec.::: Vec.VNil) vms ->
          DT.withSNat n $ makeMatArraySpec vms arrDims rowsE colsE
    _ -> error "flatDS: Given type of something other than matrix or array of matrices!"


unFlattenCW :: SL.StanName -> SL.DeclSpec t -> SL.UExpr (FlatParamT t) -> SL.CodeWriter (SL.UExpr t)
unFlattenCW sn ds e =
  let unFlatten x rowsE colsE =  SL.functionE SF.vecToMatrix (x :> rowsE :> colsE :> TNil)
  in case ds of
    SL.DeclSpec SL.StanMatrix (rowsE Vec.::: colsE Vec.::: Vec.VNil) _ -> pure $ unFlatten e rowsE colsE
    SL.ArraySpec DT.SS arrDims mds -> do
      case mds of
        SL.DeclSpec SL.StanMatrix (rowsE Vec.::: colsE Vec.::: Vec.VNil) _ -> do
          fv <- SL.declareNW $ SL.NamedDeclSpec (sn <> "_unflat") $ unFlatDS ds  -- this is wrong? (EArray (S 'n1) ECVec ~ EArray n ECVec) rather than (EArray (S n) ECVec)
          unFlattenLoop "k" rowsE colsE arrDims fv e
          pure fv
-}
