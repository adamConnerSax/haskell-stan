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
{-
data MatrixCovarianceStructure = Diagonal TE.IntE TE.IntE | Cholesky TE.IntE TE.IntE TE.EMat

data Centering = Centered | NonCentered

-- A singleton to code return type
data ReturnType t where
  SingleMatrix :: SingleMatrix TE.EMat
  ArrayOfMatrices :: TE.IntE -> ReturnType (TE.EArray1 TE.EMat)

data MuMat t = SingleMu TE.EMat | MuLikeReturn t


-- first a function for creating a LKJ-distributed Cholesky factor that we then split into pieces
matrixMultiNormalParameter :: MatrixCovarianceStructure
                           -> Centering
                           -> MuMat t
                           -> TE.EMat
                           -> ReturnType t
                           -> NamedDeclSpec t
                           -> SB.StanBuilderM md gq t
matrixMultiNormalParameter cs cent muMat scaleEM sigmaMat rt nds = do
  let flatten m = TE.functionE SF.to_vector (m :> TNil) -- column major
      unFlatten rowsE colsE v = TE.functionE SF.vecToMatrix (v :> rowsE :> colsE :> TNil)
      pName = TE.declName nds
      pDeclSpec = TE.declSpec nds
      pFlatName = pName <> "_flat"
      pFlatNDS = TE.NamedDeclSpec pFlatName pDeclSpec

  pFlat <- DAG.addBuildParameter
           $ DAG.UntransformedP pFlatNDS []
  case rt of
    SingleMatrix ->
      DAG.TransformedP nds [] TNil
      (const $ )
  in case cs of
    Diagonal rowsE colsE -> TE.functionE SF.multi_normal
-}
