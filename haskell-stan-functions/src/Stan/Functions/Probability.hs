{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

module Stan.Functions.Probability
  (
    module Stan.Functions.Probability
  )
  where
import qualified Stan.Functions.Constraints as SFC
import qualified Stan.Language.Types as SLT
import Stan.Language.Types (TypedList(..))
import qualified Stan.Language.Functions as SLF
import qualified Stan.Language.Indexing as SLI
import qualified Stan.Language.Expression as SLE
import qualified Stan.Language.Expressions as SLE

import Prelude hiding (Nat)

-- Densities & RNGs
type RealOrVec t =  (SFC.TypeOneOf t [SLT.EReal, SLT.ECVec, SLT.ERVec], SFC.GenSType t)

--rvDensity2pD :: RealOrVec t => Text -> SLF.Density t [t, t]
--rvDensity2pD = SLF.simpleDensity

rvDensity2p :: RealOrVec t => Text -> SLE.UExpr t -> SLE.UExpr t -> SLE.UExpr t -> SLE.RealE
rvDensity2p dName g p1 p2 = SLE.densityE (SLF.simpleDensity dName) g (p1 :> p2 :> TNil)

rvRNG2p :: RealOrVec t => Text -> SLE.UExpr t -> SLE.UExpr t -> SLE.UExpr t
rvRNG2p rngName p1 p2 = SLE.functionE (SLF.simpleFunction rngName) (p1 :> p2 :> TNil)

rvDensity2pS :: RealOrVec t => Text -> SLE.UExpr t -> SLE.RealE -> SLE.RealE -> SLE.RealE
rvDensity2pS dName g p1 p2 = SLE.densityE (SLF.simpleDensity dName) g (p1 :> p2 :> TNil)

rvRNG2pS :: RealOrVec t => Text -> SLE.RealE -> SLE.RealE -> SLE.UExpr t
rvRNG2pS rngName p1 p2 = SLE.functionE (SLF.simpleFunction rngName) (p1 :> p2 :> TNil)

uniform, uniform_lpdf, uniform_lupdf ::  RealOrVec t => SLF.Density t [t, t] --SLE.UExpr t -> SLE.UExpr t -> SLE.RealE
uniform = SLF.simpleDensity "uniform"
uniform_lpdf = SLF.simpleDensity "uniform_lpdf"
uniform_lupdf = SLF.simpleDensity "uniform_lupdf"

uniform_rngF :: RealOrVec t => SLF.Function t '[t]
uniform_rngF = SLF.simpleFunction "uniform_rng"

uniform_rng ::  RealOrVec t => SLE.UExpr t -> SLE.UExpr t -> SLE.UExpr t
uniform_rng = rvRNG2p "uniform_rng"

uniformS, uniformS_lpdf, uniformS_lupdf ::  RealOrVec t => SLF.Density t [SLT.EReal, SLT.EReal] --SLE.UExpr t -> SLE.RealE -> SLE.RealE -> SLE.RealE
uniformS = SLF.simpleDensity "uniform"
uniformS_lpdf = SLF.simpleDensity "uniform_lpdf"
uniformS_lupdf = SLF.simpleDensity "uniform_lupdf"

uniformS_rngF :: RealOrVec t => SLF.Function SLT.EReal '[SLT.EReal]
uniformS_rngF = SLF.simpleFunction "uniform_rng"

uniformS_rng ::  RealOrVec t => SLE.RealE -> SLE.RealE -> SLE.UExpr t
uniformS_rng = rvRNG2pS "uniform_rng"

normal, normal_lpdf, normal_lupdf ::  RealOrVec t => SLF.Density t [t,t] -- SLE.UExpr t -> SLE.UExpr t -> SLE.UExpr t -> SLE.RealE
normal = SLF.simpleDensity "normal"
normal_lpdf = SLF.simpleDensity "normal_lpdf"
normal_lupdf = SLF.simpleDensity "normal_lupdf"

normal_rngF :: RealOrVec t => SLF.Function t '[t]
normal_rngF = SLF.simpleFunction "normal_rng"

normal_rng ::  RealOrVec t => SLE.UExpr t -> SLE.UExpr t -> SLE.UExpr t
normal_rng = rvRNG2p "normal_rng"

normalS, normalS_lpdf, normalS_lupdf ::  RealOrVec t => SLF.Density t [SLT.EReal, SLT.EReal] --SLE.UExpr t -> SLE.RealE -> SLE.RealE -> SLE.RealE
normalS = SLF.simpleDensity "normal"
normalS_lpdf = SLF.simpleDensity "normal_lpdf"
normalS_lupdf = SLF.simpleDensity "normal_lupdf"

normalS_rngF :: RealOrVec t => SLF.Function t '[SLT.EReal, SLT.EReal]
normalS_rngF = SLF.simpleFunction "normal_rng"

normalS_rng ::  RealOrVec t => SLE.RealE -> SLE.RealE -> SLE.UExpr t
normalS_rng = rvRNG2pS "normal_rng"

rvDensity1p :: RealOrVec t => Text -> SLE.UExpr t -> SLE.UExpr t -> SLE.RealE
rvDensity1p dName g p = SLE.densityE (SLF.simpleDensity dName) g (p :> TNil)

rvRNG1p :: RealOrVec t => Text -> SLE.UExpr t -> SLE.UExpr t
rvRNG1p rngName p = SLE.functionE (SLF.simpleFunction rngName) (p :> TNil)

std_normal, std_normal_lpdf, std_normal_lupdf ::  RealOrVec t => SLF.Density t '[] --SLE.UExpr t -> SLE.UExpr t -> SLE.RealE
std_normal = SLF.simpleDensity "std_normal"
std_normal_lpdf = SLF.simpleDensity "std_normal_lpdf"
std_normal_lupdf = SLF.simpleDensity "std_normal_lupdf"

std_normal_rngF :: RealOrVec t => SLF.Function t '[]
std_normal_rngF = SLF.simpleFunction "std_normal_rng"

std_normal_rng ::  RealOrVec t => SLE.UExpr t
std_normal_rng = SLE.functionE std_normal_rngF TNil

lognormal, lognormal_lpdf, lognormal_lupdf ::  RealOrVec t => SLF.Density t [t, t] --SLE.UExpr t -> SLE.UExpr t -> SLE.UExpr t -> SLE.RealE
lognormal = SLF.simpleDensity "lognormal"
lognormal_lpdf = SLF.simpleDensity "lognormal_lpdf"
lognormal_lupdf = SLF.simpleDensity "lognormal_lupdf"

lognormal_rngF :: RealOrVec t => SLF.Function t [t, t]
lognormal_rngF = SLF.simpleFunction "lognormal_rng"

lognormal_rng ::  RealOrVec t => SLE.UExpr t -> SLE.UExpr t -> SLE.UExpr t
lognormal_rng = rvRNG2p "lognormal_rng"

lognormalS, lognormalS_lpdf, lognormalS_lupdf ::  RealOrVec t => SLF.Density t [SLT.EReal, SLT.EReal] --SLE.UExpr t -> SLE.RealE -> SLE.RealE -> SLE.RealE
lognormalS = SLF.simpleDensity "lognormal"
lognormalS_lpdf = SLF.simpleDensity "lognormal_lpdf"
lognormalS_lupdf = SLF.simpleDensity "lognormal_lupdf"

lognormalS_rngF :: RealOrVec t => SLF.Function t [SLT.EReal, SLT.EReal]
lognormalS_rngF = SLF.simpleFunction "lognormal_rng"

lognormalS_rng ::  RealOrVec t => SLE.RealE -> SLE.RealE -> SLE.UExpr t
lognormalS_rng = rvRNG2pS "lognormal_rng"

cauchy, cauchy_lpdf, cauchy_lupdf ::  RealOrVec t => SLF.Density t [t, t] --SLE.UExpr t -> SLE.UExpr t -> SLE.UExpr t -> SLE.RealE
cauchy = SLF.simpleDensity "cauchy"
cauchy_lpdf = SLF.simpleDensity "cauchy_lpdf"
cauchy_lupdf = SLF.simpleDensity "cauchy_lupdf"

cauchy_rngF :: RealOrVec t => SLF.Function t [t, t]
cauchy_rngF = SLF.simpleFunction "cauchy_rng"

cauchy_rng ::  RealOrVec t => SLE.UExpr t -> SLE.UExpr t -> SLE.UExpr t
cauchy_rng = rvRNG2p "cauchy_rng"

gamma, gamma_lpdf, gamma_lupdf ::  RealOrVec t => SLF.Density t [t, t] --SLE.UExpr t -> SLE.UExpr t -> SLE.UExpr t -> SLE.RealE
gamma = SLF.simpleDensity "gamma"
gamma_lpdf = SLF.simpleDensity "gamma_lpdf"
gamma_lupdf = SLF.simpleDensity "gamma_lupdf"

gamma_rngF :: RealOrVec t => SLF.Function t [t, t]
gamma_rngF = SLF.simpleFunction "gamma_rng"

gamma_rng ::  RealOrVec t => SLE.UExpr t -> SLE.UExpr t -> SLE.UExpr t
gamma_rng = rvRNG2p "gamma_rng"

beta, beta_lpdf, beta_lupdf :: RealOrVec t  => RealOrVec t => SLF.Density t [t, t] --SLE.UExpr t -> SLE.UExpr t -> SLE.UExpr t -> SLE.RealE
beta = SLF.simpleDensity "beta"
beta_lpdf = SLF.simpleDensity "beta_lpdf"
beta_lupdf = SLF.simpleDensity "beta_lupdf"

beta_rngF :: RealOrVec t => SLF.Function t [t, t]
beta_rngF = SLF.simpleFunction "beta_rng"

beta_rng ::  RealOrVec t => SLE.UExpr t -> SLE.UExpr t -> SLE.UExpr t
beta_rng = rvRNG2p "beta_rng"

betaS, betaS_lpdf, betaS_lupdf :: RealOrVec t => SLF.Density t [SLT.EReal, SLT.EReal] --SLE.UExpr t -> SLE.RealE -> SLE.RealE -> SLE.RealE
betaS = SLF.simpleDensity "beta"
betaS_lpdf = SLF.simpleDensity "beta_lpdf"
betaS_lupdf = SLF.simpleDensity "beta_lupdf"

betaS_rngF :: RealOrVec t => SLF.Function t [SLT.EReal, SLT.EReal]
betaS_rngF = SLF.simpleFunction "beta_rng"

betaS_rng ::  RealOrVec t => SLE.RealE -> SLE.RealE -> SLE.UExpr t
betaS_rng = rvRNG2pS "beta_rng"

beta_proportion, beta_proportion_lpdf, beta_proportion_lupdf :: RealOrVec t  => SLF.Density t [t, t] --RealOrVec t => SLE.UExpr t -> SLE.UExpr t -> SLE.UExpr t -> SLE.RealE
beta_proportion = SLF.simpleDensity "beta_proportion"
beta_proportion_lpdf = SLF.simpleDensity "beta_proportion_lpdf"
beta_proportion_lupdf = SLF.simpleDensity "beta_proportion_lupdf"

beta_proportion_rngF :: RealOrVec t => SLF.Function t [t, t]
beta_proportion_rngF = SLF.simpleFunction "beta_proportion_rng"

beta_proportion_rng ::  RealOrVec t => SLE.UExpr t -> SLE.UExpr t -> SLE.UExpr t
beta_proportion_rng = rvRNG2p "beta_proportion_rng"

lkj_corr_cholesky :: SLE.UExpr SLT.ESqMat -> SLE.RealE -> SLE.RealE
lkj_corr_cholesky m p = SLE.densityE (SLF.simpleDensity "lkj_corr_cholesky") m (p :> TNil)

type MultiNormalDensityC t = (SFC.TypeOneOf t [SLT.ECVec, SLT.ERVec, SLT.EArray1 SLT.ECVec, SLT.EArray1 SLT.ERVec], SFC.GenSType t)

-- the rng functions look like they return column vectors regardless of the input structure
type family MultiNormalRngReturnT t where
  MultiNormalRngReturnT SLT.ECVec = SLT.ECVec
  MultiNormalRngReturnT SLT.ERVec = SLT.ECVec
  MultiNormalRngReturnT (SLT.EArray1 SLT.ECVec) = SLT.EArray1 SLT.ECVec
  MultiNormalRngReturnT (SLT.EArray1 SLT.ERVec) = SLT.EArray1 SLT.ECVec

multiNormalDensity :: MultiNormalDensityC t => Text -> SLE.UExpr t -> SLE.UExpr t -> SLE.UExpr SLT.ESqMat -> SLE.RealE
multiNormalDensity dName c p m = SLE.densityE (SLF.simpleDensity dName) c (p :> m :> TNil)

multiNormalRNG :: (MultiNormalDensityC t, SFC.GenSType (MultiNormalRngReturnT t))
  => Text -> SLE.UExpr t -> SLE.UExpr SLT.ESqMat -> SLE.UExpr  (MultiNormalRngReturnT t)
multiNormalRNG stanName p m = SLE.functionE (SLF.simpleFunction stanName) (p :> m :> TNil)

multi_normal_cholesky, multi_normal_cholesky_lpdf, multi_normal_cholesky_lupdf ::  MultiNormalDensityC t => SLF.Density t '[t, SLT.ESqMat]
multi_normal_cholesky = SLF.simpleDensity "multi_normal_cholesky"
multi_normal_cholesky_lpdf = SLF.simpleDensity "multi_normal_cholesky_lpdf"
multi_normal_cholesky_lupdf = SLF.simpleDensity "multi_normal_cholesky_lupdf"

multi_normal_cholesky_rngF :: (MultiNormalDensityC t, SFC.GenSType (MultiNormalRngReturnT t))
                           => SLF.Function (MultiNormalRngReturnT t) [t, SLT.ESqMat]
multi_normal_cholesky_rngF = SLF.simpleFunction "multi_normal_cholesky_rng"

multi_normal_cholesky_rng :: (MultiNormalDensityC t, SFC.GenSType (MultiNormalRngReturnT t))
                          => SLE.UExpr t -> SLE.UExpr SLT.ESqMat -> SLE.UExpr  (MultiNormalRngReturnT t)
multi_normal_cholesky_rng = multiNormalRNG "multi_normal_cholesky_rng"

multi_normal, multi_normal_lpdf, multi_normal_lupdf ::  MultiNormalDensityC t => SLF.Density t [t, SLT.ESqMat]
multi_normal = SLF.simpleDensity "multi_normal"
multi_normal_lpdf = SLF.simpleDensity "multi_normal_lpdf"
multi_normal_lupdf = SLF.simpleDensity "multi_normal_lupdf"

multi_normal_rngF :: (MultiNormalDensityC t, SFC.GenSType (MultiNormalRngReturnT t))
                           => SLF.Function (MultiNormalRngReturnT t) [t, SLT.ESqMat]
multi_normal_rngF = SLF.simpleFunction "multi_normal_rng"

multi_normal_rng :: (MultiNormalDensityC t, SFC.GenSType (MultiNormalRngReturnT t))
                 =>  SLE.UExpr t -> SLE.UExpr SLT.ESqMat -> SLE.UExpr  (MultiNormalRngReturnT t)
multi_normal_rng = multiNormalRNG "multi_normal_rng"

rvDensity3p :: RealOrVec t => Text -> SLE.UExpr t -> SLE.UExpr t -> SLE.UExpr t -> SLE.UExpr t -> SLE.RealE
rvDensity3p dName g p1 p2 p3 = SLE.densityE (SLF.simpleDensity dName) g (p1 :> p2 :> p3 :> TNil)

rvRNG3p :: RealOrVec t => Text -> SLE.UExpr t -> SLE.UExpr t -> SLE.UExpr t -> SLE.UExpr t
rvRNG3p rngName p1 p2 p3 = SLE.functionE (SLF.simpleFunction rngName) (p1 :> p2 :> p3 :> TNil)

student_t, student_t_lpdf, student_t_lupdf :: RealOrVec t => SLF.Density t [t, t, t] --SLE.UExpr t -> SLE.UExpr t -> SLE.UExpr t -> SLE.UExpr t -> SLE.RealE
student_t = SLF.simpleDensity "student_t"
student_t_lpdf = SLF.simpleDensity "student_t_lpdf"
student_t_lupdf = SLF.simpleDensity "student_t_lupdf"

student_t_rngF :: RealOrVec t => SLF.Function t [t, t, t]
student_t_rngF = SLF.simpleFunction "student_t_rng"

student_t_rng :: RealOrVec t => SLE.UExpr t -> SLE.UExpr t -> SLE.UExpr t -> SLE.UExpr t
student_t_rng = rvRNG3p "student_t_rng"


type BinDensityC t t' = (SFC.TypeOneOf t [SLT.EArray1 SLT.EInt, SLT.EInt], SFC.GenSType t
                        , SFC.TypeOneOf t' [SLT.EArray1 SLT.EReal, SLT.ECVec, SLT.EReal], SLT.ScalarType t' ~ SLT.EReal, SFC.GenSType t'
                        , SLI.Dimension t ~ SLI.Dimension t')

binomialD :: BinDensityC t t' => Text -> SLE.UExpr t -> SLE.UExpr t -> SLE.UExpr t' -> SLE.RealE
binomialD stanName k n p = SLE.densityE (SLF.simpleDensity stanName) k (n :> p :> TNil)

binomial, binomial_lpmf, binomial_lupmf, binomial_logit, binomial_logit_lpmf, binomial_logit_lupmf :: BinDensityC t t'
  => SLF.Density t [t, t'] --SLE.UExpr t -> SLE.UExpr t -> SLE.UExpr t' -> SLE.RealE
binomial = SLF.simpleDensity "binomial"
binomial_lpmf = SLF.simpleDensity "binomial_lpmf"
binomial_lupmf = SLF.simpleDensity "binomial_lupmf"

binomial_rngF :: BinDensityC t t' => SLF.Function t [t, t']
binomial_rngF = SLF.simpleFunction "binomial_rng"

binomial_rng :: BinDensityC t t' => SLE.UExpr t -> SLE.UExpr t' -> SLE.UExpr t --Function t '[t, t']
binomial_rng n p = SLE.functionE (SLF.simpleFunction "binomial_rng") (n :> p :> TNil)

binomial_logit = SLF.simpleDensity "binomial_logit"
binomial_logit_lpmf = SLF.simpleDensity "binomial_logit_lpmf"
binomial_logit_lupmf = SLF.simpleDensity "binomial_logit_lupmf"

betaBinomialD :: BinDensityC t t' => Text -> SLE.UExpr t -> SLE.UExpr t -> SLE.UExpr t' -> SLE.UExpr t' -> SLE.RealE
betaBinomialD stanName k n alpha beta' = SLE.densityE (SLF.simpleDensity stanName) k (n :> alpha :> beta' :> TNil)

beta_binomial, beta_binomial_lpmf,beta_binomial_lupmf  :: BinDensityC t t' => SLF.Density t [t, t', t']
beta_binomial = SLF.simpleDensity "beta_binomial"
beta_binomial_lpmf = SLF.simpleDensity "beta_binomial_lpmf"
beta_binomial_lupmf = SLF.simpleDensity "beta_binomial_lupmf"

beta_binomial_rngF :: BinDensityC t t' => SLF.Function t [t, t', t']
beta_binomial_rngF = SLF.simpleFunction "beta_binomial_rng"

beta_binomial_rng :: BinDensityC t t' => SLE.UExpr t -> SLE.UExpr t' -> SLE.UExpr t' -> SLE.UExpr t
beta_binomial_rng n alpha beta' = SLE.functionE (SLF.simpleFunction "beta_binomial_rng") (n :> alpha :> beta' :> TNil)
{-# INLINEABLE beta_binomial_rng #-}

-- Categorical
type CategoricalTypes t = (SFC.TypeOneOf t [SLT.EInt, SLT.EIntArray], SFC.GenSType t)

categoricalD :: CategoricalTypes t => Text -> SLE.UExpr t -> SLE.VectorE -> SLE.RealE
categoricalD stanName y theta = SLE.densityE (SLF.simpleDensity stanName) y (theta :> TNil)

categorical, categorical_lpmf, categorical_lupmf  :: CategoricalTypes t => SLF.Density t '[SLT.ECVec]
categorical = SLF.simpleDensity "categorical"
categorical_lpmf = SLF.simpleDensity "categorical_lpmf"
categorical_lupmf = SLF.simpleDensity "categorical_lupmf"

categorical_rngF :: SLF.Function SLT.EInt '[SLT.ECVec]
categorical_rngF = SLF.simpleFunction "categorical_rng"

categorical_rng :: SLE.VectorE -> SLE.IntE --Function EInt '[t]
categorical_rng theta = SLE.functionE (SLF.simpleFunction "categorical_rng") (theta :> TNil)
{-# INLINEABLE categorical_rng #-}

categorical_logit, categorical_logit_lpmf, categorical_logit_lupmf :: CategoricalTypes t => SLF.Density t '[SLT.ECVec]
categorical_logit = SLF.simpleDensity "categorical_logit"
categorical_logit_lpmf = SLF.simpleDensity "categorical_logit_lpmf"
categorical_logit_lupmf = SLF.simpleDensity "categorical_logit_lupmf"

categorical_logit_rngF :: SLF.Function SLT.EInt '[SLT.ECVec]
categorical_logit_rngF = SLF.simpleFunction "categorical_logit_rng"

categorical_logit_rng :: SLE.VectorE -> SLE.IntE
categorical_logit_rng beta' = SLE.functionE (SLF.simpleFunction "categorical_logit_rng") (beta' :> TNil)

-- Multinomial
-- gamma should be on the simplex
multinomialD :: SFC.Vector t => Text -> SLE.UExpr SLT.EIntArray -> SLE.UExpr t -> SLE.RealE
multinomialD stanName ns gamma' = SLE.densityE (SLF.simpleDensity stanName) ns (gamma' :> TNil)

multinomial, multinomial_lpmf, multinomial_lupmf :: SFC.Vector t => SLF.Density SLT.EIntArray '[t]
multinomial = SLF.simpleDensity "multinomial"
multinomial_lpmf = SLF.simpleDensity "multinomial_lpmf"
multinomial_lupmf = SLF.simpleDensity "multinomial_lupmf"

multinomialRNG :: SFC.Vector t => Text -> SLE.UExpr t -> SLE.IntE -> SLE.UExpr SLT.EIntArray
multinomialRNG stanName theta' n = SLE.functionE (SLF.simpleFunction stanName) (theta' :> n :> TNil)

multinomial_rngF :: SFC.Vector t => SLF.Function SLT.EIntArray '[t, SLT.EInt]
multinomial_rngF = SLF.simpleFunction "multinomial_rng"

multinomial_rng :: SFC.Vector t => SLE.UExpr t -> SLE.IntE -> SLE.UExpr SLT.EIntArray
multinomial_rng = multinomialRNG "multinomial_rng"

multinomial_logit, multinomial_logit_lpmf, multinomial_logit_lupmf :: SFC.Vector t => SLF.Density SLT.EIntArray '[t]
multinomial_logit = SLF.simpleDensity "multinomial_logit"
multinomial_logit_lpmf = SLF.simpleDensity "multinomial_logit_lpmf"
multinomial_logit_lupmf = SLF.simpleDensity "multinomial_logit_lupmf"

multinomial_logit_rngF :: SFC.Vector t => SLE.UExpr t -> SLE.IntE -> SLE.UExpr SLT.EIntArray
multinomial_logit_rngF = multinomialRNG "multinomial_logit_rng"

multinomial_logit_rng :: SFC.Vector t => SLE.UExpr t -> SLE.IntE -> SLE.UExpr SLT.EIntArray
multinomial_logit_rng = multinomialRNG "multinomial_logit_rng"

-- dirichlet
type DirichletTypes t t' = (SFC.TypeOneOf t [SLT.ECVec, SLT.ERVec, SLT.EArray1 SLT.ECVec, SLT.EArray1 SLT.ERVec]
                           , SFC.TypeOneOf t' [SLT.ECVec, SLT.ERVec, SLT.EArray1 SLT.ECVec, SLT.EArray1 SLT.ERVec]
                           , SLI.Dimension t ~ SLI.Dimension t'
                           , SFC.GenSType t, SFC.GenSType t')

dirichletD :: DirichletTypes t t' => Text -> SLE.UExpr t -> SLE.UExpr t' -> SLE.RealE
dirichletD stanName theta alpha = SLE.densityE (SLF.simpleDensity stanName) theta (alpha :> TNil)

dirichlet, dirichlet_lpdf, dirichlet_lupdf :: DirichletTypes t t' => SLF.Density t '[t']
dirichlet = SLF.simpleDensity "dirichlet"
dirichlet_lpdf = SLF.simpleDensity "dirichlet_lpdf"
dirichlet_lupdf = SLF.simpleDensity "dirichlet_lupdf"

dirichlet_rngF :: SFC.Vector t => SLF.Function t '[t]
dirichlet_rngF = SLF.simpleFunction "dirichlet_rng"

dirichlet_rng :: SFC.Vector t => SLE.UExpr t -> SLE.UExpr t --Function t '[t]
dirichlet_rng alpha = SLE.functionE (SLF.simpleFunction "dirichlet_rng") (alpha :> TNil)
