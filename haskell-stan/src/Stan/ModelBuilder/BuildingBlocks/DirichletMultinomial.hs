{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use for_" #-}
{-# HLINT ignore "Use camelCase" #-}

module Stan.ModelBuilder.BuildingBlocks.DirichletMultinomial
  (
    module Stan.ModelBuilder.BuildingBlocks.DirichletMultinomial
  )
where

import qualified Stan.ModelBuilder.TypedExpressions.Types as TE
import Stan.ModelBuilder.TypedExpressions.TypedList (TypedList(..))
import qualified Stan.ModelBuilder.TypedExpressions.TypedList as TL
import qualified Stan.ModelBuilder.TypedExpressions.Statements as TE
import Stan.ModelBuilder.TypedExpressions.Recursion (hfmap)
import qualified Stan.ModelBuilder.TypedExpressions.Functions as TE
import qualified Stan.ModelBuilder.TypedExpressions.Operations as TEO
import qualified Stan.ModelBuilder.TypedExpressions.StanFunctions as SF

import qualified Stan.ModelBuilder as SB


import qualified Data.Vec.Lazy as Vec
import qualified Data.Type.Nat as DT
import Data.Type.Equality (type (:~:)(..))

-- These constraints are...sheesh.
addDirichletMultinomialLPMF :: forall t md gq . (TE.TypeOneOf t [TE.ECVec, TE.ERVec]
                                                , TE.TypeOneOf t [TE.ECVec, TE.ERVec, TE.EMat, TE.ESqMat, TE.ERealArray]
                                                , TE.TypeOneOf (TEO.BinaryResultT TEO.BAdd t TE.ECVec) [TE.ECVec, TE.ERVec, TE.EMat, TE.ESqMat, TE.ERealArray]
                                                , TE.GenSType t
                                                , TE.GenSType (TEO.BinaryResultT TEO.BAdd t TE.ECVec)
                                                , TE.ScalarType t ~ TE.EReal
                                                , TE.ScalarType (TEO.BinaryResultT TEO.BAdd t TE.ECVec) ~ TE.EReal
                                                )
                            => SB.StanBuilderM md gq (TE.Density TE.EIntArray '[t])
addDirichletMultinomialLPMF = do
  let f :: TE.Density TE.EIntArray '[t]
      f = TE.simpleDensity "dirichlet_multinomial_lpmf"
      sum' x = TE.functionE SF.sum (x :> TNil)
      toVector x = TE.functionE SF.to_vector (x :> TNil)
      lgamma x = TE.functionE SF.lgamma (x :> TNil)
  SB.addDensityOnce f (TE.DataArg "y" :> TE.Arg "alpha" :> TNil)
    $ \(y :> a :> TNil) ->
        TE.writerL $ (do
                         let size x = TE.functionE SF.size (x :> TNil)
                         ap <- TE.declareRHSNW (TE.NamedDeclSpec "alpha_plus" $ TE.realSpec []) $ sum' a
                         vy <- TE.declareRHSNW (TE.NamedDeclSpec "yVec" $ TE.vectorSpec (size y) []) $ toVector y
                         pure $ lgamma ap
                           `TE.plusE` sum' (lgamma (a `TE.plusE` vy))
                           `TE.minusE` lgamma (ap `TE.plusE` sum' vy)
                           `TE.minusE` sum' (lgamma a)
                     )


addDirichletMultinomialRNG :: forall t md gq . (TE.TypeOneOf t [TE.ECVec, TE.ERVec]
                                               , TE.TypeOneOf t [TE.ESimplex, TE.ECVec, TE.ERVec]
                                               , TE.GenSType t
                                               )
                           => SB.StanBuilderM md gq (TE.Function (TE.EArray1 TE.EInt) '[t, TE.EInt])
addDirichletMultinomialRNG = do
  let f :: TE.Function  (TE.EArray1 TE.EInt) [t, TE.EInt]
      f = TE.simpleFunction "dirichlet_multinomial_rng"
      dr a = TE.functionE SF.dirichlet_rng (a :> TNil)
      mr ad n = TE.functionE SF.multinomial_rng (ad :> n :> TNil)
  SB.addFunctionOnce f (TE.Arg "alpha" :> TE.Arg "N" :> TNil)
    $ \ (a :> n :> TNil) ->
        TE.writerL $ pure $ mr (dr a) n




dirichletMultinomial ::  forall t t' md gq . (TE.TypeOneOf t [TE.ECVec, TE.ERVec]
                                          , TE.TypeOneOf t' [TE.ECVec, TE.ERVec]
                                          , TE.TypeOneOf t' [TE.ESimplex, TE.ECVec, TE.ERVec]
                                          , TE.TypeOneOf t [TE.ECVec, TE.ERVec, TE.EMat, TE.ESqMat, TE.ERealArray]
                                          , TE.TypeOneOf (TEO.BinaryResultT TEO.BAdd t TE.ECVec) [TE.ECVec, TE.ERVec, TE.EMat, TE.ESqMat, TE.ERealArray]
                                          , TE.GenSType t
                                          , TE.GenSType t'
                                          , TE.GenSType (TEO.BinaryResultT TEO.BAdd t TE.ECVec)
                                          , TE.ScalarType t ~ TE.EReal
                                          , TE.ScalarType (TEO.BinaryResultT TEO.BAdd t TE.ECVec) ~ TE.EReal
                                          )
                     => SB.StanBuilderM md gq (TE.Density TE.EIntArray '[t]
                                              , TE.Density TE.EIntArray '[t]
                                              , TE.Function TE.EIntArray '[t', TE.EInt]
                                              )
dirichletMultinomial = do
  lpmf <- addDirichletMultinomialLPMF @t
  rng <- addDirichletMultinomialRNG @t'
  pure (TE.simpleDensity "dirichlet_multinomial", lpmf, rng)
