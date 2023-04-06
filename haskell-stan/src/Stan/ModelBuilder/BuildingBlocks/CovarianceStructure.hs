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
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use for_" #-}
{-# HLINT ignore "Use camelCase" #-}
{-# LANGUAGE QuantifiedConstraints #-}

module Stan.ModelBuilder.BuildingBlocks.CovarianceStructure
  (
    module Stan.ModelBuilder.BuildingBlocks.CovarianceStructure
  )
where


import qualified Stan.ModelBuilder.TypedExpressions.Types as TE
import Stan.ModelBuilder.TypedExpressions.TypedList (TypedList(..))
import qualified Stan.ModelBuilder.TypedExpressions.Statements as TE
import qualified Stan.ModelBuilder.TypedExpressions.Indexing as TE
import qualified Stan.ModelBuilder.TypedExpressions.Operations as TE
import qualified Stan.ModelBuilder.TypedExpressions.StanFunctions as SF
import qualified Stan.ModelBuilder.TypedExpressions.DAGTypes as DAG
import qualified Stan.ModelBuilder as SB
import qualified Stan.ModelBuilder.Distributions as SMD

import Prelude hiding (sum, All)
import qualified Data.Dependent.HashMap as DHash
import qualified Data.Vector.Unboxed as VU
import qualified Stan.ModelConfig as SB
import Stan.ModelBuilder.BuilderTypes (dataSetSizeName)

data MatrixCovarianceStructure = Diagonal TE.IntE TE.IntE | Cholesky TE.IntE TE.IntE TE.MatrixE

data Centering = Centered | NonCentered

-- A singleton to code return type
--data ReturnType t where
--  SingleMatrix :: SingleMatrix TE.MatrixE
--  ArrayOfMatrices :: TE.IntE -> ReturnType (TE.EArray1 TE.EMat)

data MuMat t where
  SingleMu :: TE.EMat -> MuMat TE.MatrixE
  ArrayMu :: TE.ArrayE TE.EMat -> MuMat (TE.EArray1 TE.EMat)

matrixMultiNormalParameter :: MatrixCovarianceStructure
                           -> Centering
                           -> MuMat t
                           -> TE.MatrixE
                           -> NamedDeclSpec t
                           -> SB.StanBuilderM md gq t
matrixMultiNormalParameter cs cent muMat scaleEM sigmaMat nds = do
  let flatten m = TE.functionE SF.to_vector (m :> TNil) -- column major
      unFlatten rowsE colsE v = TE.functionE SF.vecToMatrix (v :> rowsE :> colsE :> TNil)
      multiNormal x mu lSigma = TE.sampleE x SF.multi_normal_cholesky (mu :> lSigma :> TNil)
      pName = TE.declName nds
      pDeclSpec = TE.declSpec nds
      pFlatName = pName <> "_flat"
      pFlatNDS = TE.NamedDeclSpec pFlatName pDeclSpec

  p <- DAG.addBuildParameter $ DAG.UntransformedP nds [] (\_ _ -> pure ())
  case muMat of
    SingleMu m -> do
      DAG.TransformedP pFlatNDS [] (p :> TNil) DAG.ModelBlockLocal
      (\(p :> TNil) -> DAG.DeclRHS $ flatten p)
      (m :> sigmaMat :> TNil)
      (\(mu :> sigma :> TNil) vFlat -> multiNormal vFlat (flatten mu) (flatten sigma))
--    ArrayOfMatrices n
