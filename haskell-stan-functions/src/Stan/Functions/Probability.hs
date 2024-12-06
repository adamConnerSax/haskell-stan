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
import qualified Stan.Language.TypedList as SLTL
import Stan.Language.TypedList (TypedList(..))
import qualified Stan.Language.Functions as SLF
import qualified Stan.Language.Indexing as SLI
import qualified Stan.Language.Expressions as SLE

import qualified GHC.TypeLits as TE
import GHC.TypeLits (ErrorMessage((:<>:)))
import Data.Type.Nat (SNatI)
import Data.Type.Equality (type (~))
import Prelude hiding (Nat)


-- Densities & RNGs
type RealOrVec t =  (SFC.TypeOneOf t [SLT.EReal, SLT.ECVec, SLT.ERVec], SFC.GenSType t)


rvDensity2p :: RealOrVec t => Text -> SLE.UExpr t -> SLE.UExpr t -> SLE.UExpr t -> SLE.RealE
rvDensity2p dName g p1 p2 = SLE.densityE (SLF.simpleDensity dName) g (p1 :> p2 :> TNil)

rvRNG2p :: RealOrVec t => Text -> SLE.UExpr t -> SLE.UExpr t -> SLE.UExpr t
rvRNG2p rngName p1 p2 = SLE.functionE (SLF.simpleFunction rngName) (p1 :> p2 :> TNil)

rvDensity2pS :: RealOrVec t => Text -> SLE.UExpr t -> SLE.RealE -> SLE.RealE -> SLE.RealE
rvDensity2pS dName g p1 p2 = SLE.densityE (SLF.simpleDensity dName) g (p1 :> p2 :> TNil)

rvRNG2pS :: RealOrVec t => Text -> SLE.RealE -> SLE.RealE -> SLE.UExpr t
rvRNG2pS rngName p1 p2 = SLE.functionE (SLF.simpleFunction rngName) (p1 :> p2 :> TNil)

uniform, uniform_lpdf, uniform_lupdf ::  RealOrVec t => SLE.UExpr t -> SLE.UExpr t -> SLE.UExpr t -> SLE.RealE
uniform = rvDensity2p "uniform"
uniform_lpdf = rvDensity2p "uniform_lpdf"
uniform_lupdf = rvDensity2p "uniform_lupdf"

uniform_rng ::  RealOrVec t => SLE.UExpr t -> SLE.UExpr t -> SLE.UExpr t
uniform_rng = rvRNG2p "uniform_rng"

uniformS, uniformS_lpdf, uniformS_lupdf ::  RealOrVec t => SLE.UExpr t -> SLE.RealE -> SLE.RealE -> SLE.RealE
uniformS = rvDensity2pS "uniform"
uniformS_lpdf = rvDensity2pS "uniform_lpdf"
uniformS_lupdf = rvDensity2pS "uniform_lupdf"

uniformS_rng ::  RealOrVec t => SLE.RealE -> SLE.RealE -> SLE.UExpr t
uniformS_rng = rvRNG2pS "uniform_rng"

normal, normal_lpdf, normal_lupdf ::  RealOrVec t => SLE.UExpr t -> SLE.UExpr t -> SLE.UExpr t -> SLE.RealE
normal = rvDensity2p "normal"
normal_lpdf = rvDensity2p "normal_lpdf"
normal_lupdf = rvDensity2p "normal_lupdf"

normal_rng ::  RealOrVec t => SLE.UExpr t -> SLE.UExpr t -> SLE.UExpr t
normal_rng = rvRNG2p "normal_rng"

normalS, normalS_lpdf, normalS_lupdf ::  RealOrVec t => SLE.UExpr t -> SLE.RealE -> SLE.RealE -> SLE.RealE
normalS = rvDensity2pS "normal"
normalS_lpdf = rvDensity2pS "normal_lpdf"
normalS_lupdf = rvDensity2pS "normal_lupdf"

normalS_rng ::  RealOrVec t => SLE.RealE -> SLE.RealE -> SLE.UExpr t
normalS_rng = rvRNG2pS "normal_rng"

rvDensity1p :: RealOrVec t => Text -> SLE.UExpr t -> SLE.UExpr t -> SLE.RealE
rvDensity1p dName g p = SLE.densityE (SLF.simpleDensity dName) g (p :> TNil)

rvRNG1p :: RealOrVec t => Text -> SLE.UExpr t -> SLE.UExpr t
rvRNG1p rngName p = SLE.functionE (SLF.simpleFunction rngName) (p :> TNil)

std_normal, std_normal_lpdf, std_normal_lupdf ::  RealOrVec t => SLE.UExpr t -> SLE.UExpr t -> SLE.RealE
std_normal = rvDensity1p "std_normal"
std_normal_lpdf = rvDensity1p "std_normal_lpdf"
std_normal_lupdf = rvDensity1p "std_normal_lupdf"

std_normal_rng ::  RealOrVec t => SLE.UExpr t -> SLE.UExpr t
std_normal_rng = rvRNG1p "std_normal_rng"

lognormal, lognormal_lpdf, lognormal_lupdf ::  RealOrVec t => SLE.UExpr t -> SLE.UExpr t -> SLE.UExpr t -> SLE.RealE
lognormal = rvDensity2p "lognormal"
lognormal_lpdf = rvDensity2p "lognormal_lpdf"
lognormal_lupdf = rvDensity2p "lognormal_lupdf"

lognormal_rng ::  RealOrVec t => SLE.UExpr t -> SLE.UExpr t -> SLE.UExpr t
lognormal_rng = rvRNG2p "lognormal_rng"

lognormalS, lognormalS_lpdf, lognormalS_lupdf ::  RealOrVec t => SLE.UExpr t -> SLE.RealE -> SLE.RealE -> SLE.RealE
lognormalS = rvDensity2pS "lognormal"
lognormalS_lpdf = rvDensity2pS "lognormal_lpdf"
lognormalS_lupdf = rvDensity2pS "lognormal_lupdf"

lognormalS_rng ::  RealOrVec t => SLE.RealE -> SLE.RealE -> SLE.UExpr t
lognormalS_rng = rvRNG2pS "lognormal_rng"

cauchy, cauchy_lpdf, cauchy_lupdf ::  RealOrVec t => SLE.UExpr t -> SLE.UExpr t -> SLE.UExpr t -> SLE.RealE
cauchy = rvDensity2p "cauchy"
cauchy_lpdf = rvDensity2p "cauchy_lpdf"
cauchy_lupdf = rvDensity2p "cauchy_lupdf"

cauchy_rng ::  RealOrVec t => SLE.UExpr t -> SLE.UExpr t -> SLE.UExpr t
cauchy_rng = rvRNG2p "cauchy_rng"

gamma, gamma_lpdf, gamma_lupdf ::  RealOrVec t => SLE.UExpr t -> SLE.UExpr t -> SLE.UExpr t -> SLE.RealE
gamma = rvDensity2p "gamma"
gamma_lpdf = rvDensity2p "gamma_lpdf"
gamma_lupdf = rvDensity2p "gamma_lupdf"

gamma_rng ::  RealOrVec t => SLE.UExpr t -> SLE.UExpr t -> SLE.UExpr t
gamma_rng = rvRNG2p "gamma_rng"

beta, beta_lpdf, beta_lupdf :: RealOrVec t  => RealOrVec t => SLE.UExpr t -> SLE.UExpr t -> SLE.UExpr t -> SLE.RealE
beta = rvDensity2p "beta"
beta_lpdf = rvDensity2p "beta_lpdf"
beta_lupdf = rvDensity2p "beta_lupdf"

beta_rng ::  RealOrVec t => SLE.UExpr t -> SLE.UExpr t -> SLE.UExpr t
beta_rng = rvRNG2p "beta_rng"

betaS, betaS_lpdf, betaS_lupdf :: RealOrVec t  => RealOrVec t => SLE.UExpr t -> SLE.RealE -> SLE.RealE -> SLE.RealE
betaS = rvDensity2p "beta"
betaS_lpdf = rvDensity2p "beta_lpdf"
betaS_lupdf = rvDensity2p "beta_lupdf"

betaS_rng ::  RealOrVec t => SLE.RealE -> SLE.RealE t -> SLE.UExpr t
betaS_rng = rvRNG2p "beta_rng"

beta_proportion, beta_proportion_lpdf, beta_proportion_lupdf :: RealOrVec t  => RealOrVec t => SLE.UExpr t -> SLE.UExpr t -> SLE.UExpr t -> SLE.RealE
beta_proportion = rvDensity2p "beta_proportion"
beta_proportion_lpdf = rvDensity2p "beta_proportion_lpdf"
beta_proportion_lupdf = rvDensity2p "beta_proportion_lupdf"

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
  => SLE.UExpr t -> SLE.UExpr SLT.ESqMat -> SLE.UExpr  (MultiNormalRngReturnT t)
multiNormalRNG rngName p m = SLE.functionE (SLF.simpleFunction rngName) (p :> m :> TNil)

multi_normal_cholesky, multi_normal_cholesky_lpdf, multi_normal_cholesky_lupdf ::  MultiNormalDensityC t
  => SLE.UExpr t -> SLE.UExpr t -> SLE.UExpr SLT.ESqMat -> SLE.RealE
multi_normal_cholesky = multiNormalDensity "multi_normal_cholesky"
multi_normal_cholesky_lpdf = multiNormalDensity "multi_normal_cholesky_lpdf"
multi_normal_cholesky_lupdf = multiNormalDensity "multi_normal_cholesky_lupdf"

multi_normal_cholesky_rng :: (MultiNormalDensityC t, SFC.GenSType (MultiNormalRngReturnT t))
  => SLE.UExpr t -> SLE.UExpr SLT.ESqMat -> SLE.UExpr  (MultiNormalRngReturnT t)
multi_normal_cholesky_rng = multiNormalRNG "multi_normal_cholesky_rng"

multi_normal, multi_normal_lpdf, multi_normal_lupdf ::  MultiNormalDensityC t
  => SLE.UExpr t -> SLE.UExpr t -> SLE.UExpr SLT.ESqMat -> SLE.RealE
multi_normal = multiNormalDensity "multi_normal"
multi_normal_lpdf = multiNormalDensity "multi_normal_lpdf"
multi_normal_lupdf = multiNormalDensity "multi_normal_lupdf"

multi_normal_rng :: (MultiNormalDensityC t, SFC.GenSType (MultiNormalRngReturnT t))
                 =>  SLE.UExpr t -> SLE.UExpr SLT.ESqMat -> SLE.UExpr  (MultiNormalRngReturnT t)
multi_normal_rng = multiNormalRNG "multi_normal_rng"

rvDensity3p :: RealOrVec t => Text -> SLE.UExpr t -> SLE.UExpr t -> SLE.UExpr t -> SLE.UExpr t -> SLE.RealE
rvDensity3p dName g p1 p2 p3 = SLE.densityE (SLF.simpleDensity dName) g (p1 :> p2 :> p3 :> TNil)

rvRNG3p :: RealOrVec t => Text -> SLE.UExpr t -> SLE.UExpr t -> SLE.UExpr t -> SLE.UExpr t
rvRNG3p rngName p1 p2 p3 = SLE.functionE (SLF.simpleFunction rngName) (p1 :> p2 :> p3 :> TNil)

student_t, student_t_lpdf, student_t_lupdf :: RealOrVec t => SLE.UExpr t -> SLE.UExpr t -> SLE.UExpr t -> SLE.UExpr t -> SLE.RealE
student_t = rvDensity3p "student_t"
student_t_lpdf = rvDensity3p "student_t_lpdf"
student_t_lupdf = rvDensity3p "student_t_lupdf"

student_t_rng :: RealOrVec t => SLE.UExpr t -> SLE.UExpr t -> SLE.UExpr t -> SLE.UExpr t
student_t_rng = rvRNG3p "student_t_rng"


type BinDensityC t t' = (SFC.TypeOneOf t [SLT.EArray1 SLT.EInt, SLT.EInt], SFC.GenSType t
                        , SFC.TypeOneOf t' [SLT.EArray1 SLT.EReal, SLT.ECVec, SLT.EReal], SLT.ScalarType t' ~ SLT.EReal, SFC.GenSType t'
                        , SLI.Dimension t ~ SLI.Dimension t')

binomialD :: BinDensityC t t' => Text -> SLE.UExpr t -> SLE.UExpr t -> SLE.UExpr t' -> SLE.RealE
binomialD stanName k n p = SLE.densityE (SLF.simpleDensity stanName) k (n :> p :> TNil)

binomial, binomial_lpdf, binomial_lupdf, binomial_logit, binomial_logit_lpdf, binomial_logit_lupdf :: BinDensityC t t'
  => SLE.UExpr t -> SLE.UExpr t -> SLE.UExpr t' -> SLE.RealE
binomial = binomialD "binomial"
binomial_lpdf = binomialD "binomial_lpdf"
binomial_lupdf = binomialD "binomial_lupdf"

binomial_rng :: BinDensityC t t' => SLE.UExpr t -> SLE.UExpr t' -> SLE.UExpr t --Function t '[t, t']
binomial_rng n p = SLE.functionE (SLF.simpleFunction "binomial_rng") (n :> p :> TNil)

binomial_logit = binomialD "binomial_logit"
binomial_logit_lpdf = binomialD "binomial_logit_lpdf"
binomial_logit_lupdf = binomialD "binomial_logit_lupdf"

betaBinomialD :: BinDensityC t t' => Text -> SLE.UExpr t -> SLE.UExpr t -> SLE.UExpr t' -> SLE.UExpr t' -> SLE.RealE
betaBinomialD stanName k n alpha beta = SLE.densityE (SLF.simpleDensity stanName) k (n :> alpha :> beta :> TNil)
beta_binomial = betaBinomialD "beta_binomial"
beta_binomial_lpmf = betaBinomialD "beta_binomial_lpmf"
beta_binomial_lupmf = betaBinomialD "beta_binomial_lupmf"

beta_binomial_rng :: BinDensityC t t' => SLE.UExpr t -> SLE.UExpr t' -> SLE.UExpr t' -> SLE.UExpr t
beta_binomial_rng n alpha beta = SLE.functionE (SLF.simpleFunction "beta_binomial_rng") (n :> alpha :> beta :> TNil)
{-# INLINEABLE beta_binomial_rng #-}

-- Categorical
type CategoricalTypes t = (SFC.TypeOneOf t [SLT.EInt, SLT.EIntArray], SFC.GenSType t)

categoricalD :: CategoricalTypes t => Text -> SLE.UExpr t -> SLE.VectorE -> SLE.RealE
categoricalD stanName y theta = SLE.densityE (SLF.simpleDensity stanName) y (theta :> TNil)
categorical = categoricalD "categorical"
categorical_lpmf = categoricalD "categorical_lpmf"
categorical_lupmf = catefgoricalD "categorical_lupmf"

categorical_rng :: SLE.VectorE -> SLE.IntE --Function EInt '[t]
categorical_rng theta = SLE.functionE (SLF.simpleFunction "categorical_rng") (theta :> TNil)
{-# INLINEABLE categorical_rng #-}


categorical_logit, categorical_logit_lpmf, categorical_logit_lupmf :: CategoricalLogitTypes t
  => TE.UExpr t -> TE.VectorE -> TE.RealE
categorical_logit = categoricalD "categorical_logit"
categorical_logit_lpmf = categoricalD "categorical_logit_lpmf"
categorical_logit_lupmf = categoricalD "categorical_logit_lupmf"

categorical_logit_rng :: SLE.VectorE -> SLE.IntE
categorical_logit_rng beta = SLE.functionE (SLF.simpleFunction "categorical_logit_rng") (beta :> TNil)

-- HERE

-- Multinomial
multinomial :: (TypeOneOf t [ESimplex, ECVec, ERVec], GenSType t) => Density EIntArray '[t]
multinomial = simpleDensity "multinomial"
{-# INLINEABLE multinomial #-}

multinomial_lpmf :: (TypeOneOf t [ESimplex, ECVec, ERVec], GenSType t) => Density EIntArray '[t]
multinomial_lpmf = simpleDensity "multinomial_lpmf"
{-# INLINEABLE multinomial_lpmf #-}

multinomial_lupmf :: (TypeOneOf t [ESimplex, ECVec, ERVec], GenSType t) => Density EIntArray '[t]
multinomial_lupmf = simpleDensity "multinomial_lupmf"
{-# INLINEABLE multinomial_lupmf #-}

multinomial_rng :: (TypeOneOf t [ESimplex, ECVec, ERVec], GenSType t) => Function EIntArray '[t, EInt]
multinomial_rng = simpleFunction "multinomial_rng"
{-# INLINEABLE multinomial_rng #-}

multinomial_logit :: (TypeOneOf t [ECVec, ERVec], GenSType t) =>  Density EIntArray '[t]
multinomial_logit = simpleDensity "multinomial_logit"
{-# INLINEABLE multinomial_logit #-}

multinomial_logit_lpmf ::  (TypeOneOf t [ECVec, ERVec], GenSType t) => Density EIntArray '[t]
multinomial_logit_lpmf = simpleDensity "multinomial_logit_lpmf"
{-# INLINEABLE multinomial_logit_lpmf #-}

multinomial_logit_lupmf ::  (TypeOneOf t [ECVec, ERVec], GenSType t) => Density EIntArray '[t]
multinomial_logit_lupmf = simpleDensity "multinomial_logit_lupmf"
{-# INLINEABLE multinomial_logit_lupmf #-}

multinomial_logit_rng :: Function EIntArray '[ECVec, EInt]
multinomial_logit_rng = simpleFunction "multinomial_logit_rng"
{-# INLINEABLE multinomial_logit_rng #-}

-- dirichlet
type DirichletTypes t t' = (TypeOneOf t [ECVec, ERVec, ESimplex, EArray1 ECVec, EArray1 ERVec, EArray1 ESimplex]
                           , TypeOneOf t' [ECVec, ERVec, EArray1 ECVec, EArray1 ERVec]
                           , Dimension t ~ Dimension t'
                           , GenSType t, GenSType t')

dirichlet :: DirichletTypes t t' => Density t '[t']
dirichlet = simpleDensity "dirichlet"
{-# INLINEABLE dirichlet #-}

dirichlet_lupdf :: DirichletTypes t t' => Density t '[t']
dirichlet_lupdf = simpleDensity "dirichlet_lupdf"
{-# INLINEABLE dirichlet_lupdf #-}

dirichlet_lpdf :: DirichletTypes t t' => Density t '[t']
dirichlet_lpdf = simpleDensity "dirichlet_lpdf"
{-# INLINEABLE dirichlet_lpdf #-}

dirichlet_rng :: (TypeOneOf t [ECVec, ERVec], GenSType t) => Function t '[t]
dirichlet_rng = simpleFunction "dirichlet_rng"
{-# INLINEABLE dirichlet_rng #-}
