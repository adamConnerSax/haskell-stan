{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use for_" #-}
{-# HLINT ignore "Use camelCase" #-}

module Stan.BuildingBlocks.DirichletMultinomial
  (
    module Stan.BuildingBlocks.DirichletMultinomial
  )
where

import qualified Stan.Language as SL
import Stan.Language (TypedList(..))
import qualified Stan.Functions as SF
import Stan.Functions.Operators
import qualified Stan.Builder as SB

import Effectful (Eff)

-- These constraints are...sheesh.
addDirichletMultinomialLPMF :: forall t es . (SB.StanFunctionsC es
                                             , SF.RealContainer t
                                             , SF.RealContainer (SL.BinaryResultT SL.BAdd t SL.ECVec)
                                             )
                            => Eff es (SL.Density SL.EIntArray '[t])
addDirichletMultinomialLPMF = do
  let f :: SL.Density SL.EIntArray '[t]
      f = SL.simpleDensity "dirichlet_multinomial_lpmf"
  SB.addDensityOnce f (SL.DataArg "y" :> SL.Arg "alpha" :> TNil)
    $ \(y :> a :> TNil) ->
        SL.cwStmt $ (do
                        ap <- SL.declareRHSNW (SL.NamedDeclSpec "alpha_plus" $ SL.realSpec) $ SF.sum a
                        vy <- SL.declareRHSNW (SL.NamedDeclSpec "yVec" $ SL.vectorSpec (SF.size y)) $ SF.to_vector y
                        pure $ SF.lgamma ap |+| SF.sum (SF.lgamma (a |+| vy)) |-| SF.lgamma (ap |+| SF.sum vy) |-| SF.sum (SF.lgamma a)
{-                              `SL.plusE` sum' (lgamma (a `SL.plusE` vy))
                              `SL.minusE` lgamma (ap `SL.plusE` sum' vy)
                              `SL.minusE` sum' (lgamma a)
-}
                    )

addDirichletMultinomialRNG :: forall t es . (SB.StanFunctionsC es
                                            , SL.TypeOneOf t [SL.ECVec, SL.ERVec]
                                            , SL.GenSType t
                                               )
                           => Eff es (SL.Function (SL.EArray1 SL.EInt) '[t, SL.EInt])
addDirichletMultinomialRNG = do
  let f :: SL.Function  (SL.EArray1 SL.EInt) [t, SL.EInt]
      f = SL.simpleFunction "dirichlet_multinomial_rng"
--      dr a = SL.functionE SF.dirichlet_rng (a :> TNil)
--      mr ad n = SL.functionE SF.multinomial_rng (ad :> n :> TNil)
  SB.addFunctionOnce f (SL.Arg "alpha" :> SL.Arg "N" :> TNil)
    $ \ (a :> n :> TNil) -> SL.cwStmt $ pure $ SF.multinomial_rng (SF.dirichlet_rng a) n

dirichletMultinomial ::  forall t t' es . (SB.StanFunctionsC es
                                          , SL.TypeOneOf t' [SL.ECVec, SL.ERVec]
                                          , SF.RealContainer t
                                          , SF.RealContainer (SL.BinaryResultT SL.BAdd t SL.ECVec)
                                          , SL.GenSType t'
                                          )
                     => Eff es (SL.Density SL.EIntArray '[t]
                               , SL.Density SL.EIntArray '[t]
                               , SL.Function SL.EIntArray '[t', SL.EInt]
                               , SL.UExpr t' -> SL.IntE -> SL.IntArrayE
                               )
dirichletMultinomial = do
  lpmf <- addDirichletMultinomialLPMF @t
  rng <- addDirichletMultinomialRNG @t'
  pure (SL.simpleDensity "dirichlet_multinomial", lpmf, rng, \t' n -> SL.functionE rng (t' :> n :> TNil))
