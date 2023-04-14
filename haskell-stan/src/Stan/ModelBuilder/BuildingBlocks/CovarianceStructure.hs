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

import qualified Data.Vec.Lazy as Vec
import qualified Data.Type.Nat as DT

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

type family FlatParamT t where
  FlatParamT TE.EMat = TE.ECVec
  FlatParamT (TE.EArray n TE.EMat) = TE.EArray n TE.ECVec
{-
type ArrayOfMatricesSpec n = TE.DeclSpec (TE.StanArray (DT.SNat n) TE.EMat)

vecDimMatrix :: Vec.Vec DT.Nat2 TE.IntE -> TE.DeclSpec TE.StanMatrix
vecDimMatrix (rowsE Vec.::: colsE Vec.::: Vec.VNil) = TE.matrixSpec rowsE colsE []
-}

type ArrayMatDims n = (Vec.Vec n TE.IntE, Vec.Vec DT.Nat2 TE.IntE)

arrayMatDims :: DT.SNatI m => Vec.Vec (m `DT.Plus` DT.Nat2) TE.IntE -> ArrayMatDims m
arrayMatDims = Vec.split

makeVecArraySpec :: DT.SNatI m => [TE.VarModifier TE.UExpr (TE.ScalarType TE.EReal)]
                 -> Vec.Vec (m `DT.Plus` DT.Nat2) TE.IntE
                 -> TE.DeclSpec (TE.EArray m TE.ECVec)
makeVecArraySpec vms v =
  let (aDims, mDims) = arrayMatDims v
      (rowsE Vec.::: colsE Vec.::: Vec.VNil) = mDims
  in TE.arraySpec DT.snat aDims $ TE.vectorSpec (rowsE `TE.timesE`colsE) vms

flatDS :: forall t . ParamC t => TE.DeclSpec t -> TE.DeclSpec (FlatParamT t)
flatDS ds =
  case ds of
    TE.DeclSpec TE.StanMatrix (rowsE Vec.::: colsE Vec.::: Vec.VNil) vms ->
      TE.vectorSpec (rowsE `TE.timesE` colsE) vms
    TE.DeclSpec (TE.StanArray n TE.StanMatrix) dims vms ->
      DT.withSNat n $ makeVecArraySpec vms dims

flatNDS :: ParamC t => TE.NamedDeclSpec t -> TE.NamedDeclSpec (FlatParamT t)
flatNDS nds = TE.NamedDeclSpec (TE.declName nds <> "_flat") $ flatDS $ TE.decl nds

{-indexVec :: TL.TypedList TE.UExpr (TL.SameTypeList TE.EInt n) -> Vec.Vec n TE.IntE
indexVec TNil = Vec.VNil
indexVec tl = go tl Vec.VNil
  where
    go :: TL.TypedList TE.UExpr (TL.SameTypeList TE.EInt n) -> Vec.Vec m TE.IntE -> Vec.Vec (DT.S m) TE.IntE
    go (ie :> TNil) v = ie Vec.::: v
    go (ie :> ies) v = go ies (ie Vec.::: v)
-}

flattenCW :: ParamC t
  => TE.StanName -> TE.DeclSpec t -> TE.UExpr t -> TE.CodeWriter (TE.UExpr (FlatParamT t))
flattenCW sn ds e =
  let flatten e =  TE.functionE SF.to_vector (e :> TNil)
  in case ds of
  TE.DeclSpec TE.StanMatrix _ _ -> pure $ flatten e
  TE.DeclSpec (TE.StanArray n TE.StanMatrix) dims _ -> do
    fv <- TE.declareNW $ TE.NamedDeclSpec (sn <> "_flat") $ flatDS ds
    DT.withSNat n $ do
      let (aDims, _) = arrayMatDims dims
      TE.addStmt
        $ TE.intVecLoops "k" aDims

      aSizeE "k" $ \k -> (fv `TE.at` k) `TE.assign` flatten (e `TE.at` k)
    pure fv

data ParamMat t where
  SingleParam :: TE.MatrixE -> ParamMat TE.EMat
  ArrayParam :: TE.ArrayE TE.EMat -> ParamMat (TE.EArray1 TE.EMat)

{-
matrixMultiNormalParameter :: MatrixCovarianceStructure
                           -> Centering
                           -> ParamMat t
                           -> TE.MatrixE
                           -> TE.NamedDeclSpec t
                           -> SB.StanBuilderM md gq (TE.UExpr t)
matrixMultiNormalParameter cs cent pMat sigmaMat nds = do
  let flatten m = case TE.toSType m of
        TE.EMat -> TE.functionE SF.to_vector (m :> TNil) -- column major
        TE.EArray1 TE.EMat ->
--      unFlatten rowsE colsE v = TE.functionE SF.vecToMatrix (v :> rowsE :> colsE :> TNil)

      multiNormalC x mu lSigma = TE.sample x SF.multi_normal_cholesky (mu :> lSigma :> TNil)
--      multiNormalD x mu sigma = TE.sample x SF.normal (mu :> sigma :> TNil)

  p <- DAG.addBuildParameter $ DAG.UntransformedP nds [] TNil (\_ _ -> pure ())
  let multiNormalPrior :: ParamC t => TE.ExprList '[t, TE.EMat] -> TE.UExpr (FlatParamT t) -> TE.CodeWriter ()
      multiNormalPrior (mu :> sigma :> TNil) lpFlat = do
        flatMu <- case TE.toSType m of
          TE.EMat -> pure $ TE.functionE SF.to_vector (m :> TNil)
          TE.EArray1 TE.EMat -> do
            fm <- TE.declareNW (TE.NamedDeclSpec "")
        case cs of
          Diagonal -> void $ TE.addStmt $ TE.sample lpFlat SF.normal (flatten mu :> flatten sigma :> TNil) --multiNormalD lpFlat (flatten mu) (flatten sigma)
          Cholesky cf -> do
            let cM = TE.functionE SF.diagPostMultiply (cf :> flatten sigma :> TNil)
            TE.addStmt $ multiNormalC lpFlat (flatten mu) cM
            pure ()
  case pMat of
    SingleParam m -> do
      let lp = DAG.TransformedP (flatNDS nds) [] (p :> TNil) DAG.ModelBlockLocal
               (\(p :> TNil) -> DAG.DeclRHS $ flatten p)
               (m :> sigmaMat :> TNil)
               multiNormalPrior
      _ <- DAG.addBuildParameter lp
      pure ()
    ArrayParam am -> do
      let sizeE = SBB.arr1LengthE am
          lp = DAG.TransformedP (flatVar nds) [] (p :> TNil) DAG.ModelBlockLocal
              (\(p :> TNil) -> DeclCodeF
                               $ \lhs -> TE.loopSized sizeE "k"
                                         $ \k -> lhs `TE.at` k `TE.assign` flatten (p `TE.at` k)

              )
              (am :> sigmaMat :> TNil)
              multiNormalPrior
      _ <- DAG.addBuildParameter lp
      pure ()
  pure p
-}
