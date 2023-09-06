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

module Stan.ModelBuilder.TypedExpressions.StanFunctions
  (
    module Stan.ModelBuilder.TypedExpressions.StanFunctions
  , module Stan.ModelBuilder.TypedExpressions.Functions
  )
  where

import Stan.ModelBuilder.TypedExpressions.Types
import Stan.ModelBuilder.TypedExpressions.TypedList
import Stan.ModelBuilder.TypedExpressions.Functions
import Stan.ModelBuilder.TypedExpressions.Indexing
import Stan.ModelBuilder.TypedExpressions.Expressions

import qualified GHC.TypeLits as TE
import GHC.TypeLits (ErrorMessage((:<>:)))
import Data.Type.Nat (SNatI)
import Data.Type.Equality (type (~))
import Prelude hiding (Nat)

-- this needs fixingf for higher dimensi
type VectorizedReal t = (GenSType t, ScalarType t ~ EReal)

logit :: VectorizedReal t => Function t '[t]
logit = simpleFunction "logit"
{-# INLINEABLE logit #-}
--logit :: TE.ExprList '[EReal] -> TE

inv_logit :: VectorizedReal t => Function t '[t]
inv_logit = simpleFunction "inv_logit"
{-# INLINEABLE inv_logit #-}

sqrt :: VectorizedReal t => Function t '[t]
sqrt = simpleFunction "sqrt"
{-# INLINEABLE sqrt #-}

inv_sqrt :: VectorizedReal t => Function t '[t]
inv_sqrt = simpleFunction "inv_sqrt"
{-# INLINEABLE inv_sqrt #-}

lgamma :: VectorizedReal t => Function t '[t]
lgamma = simpleFunction "lgamma"
{-# INLINEABLE lgamma #-}

log :: VectorizedReal t => Function t '[t]
log = simpleFunction "log"
{-# INLINEABLE log #-}

exp :: VectorizedReal t => Function t '[t]
exp = simpleFunction "exp"
{-# INLINEABLE exp #-}


log1m :: VectorizedReal t => Function t '[t]
log1m = simpleFunction "log1m"
{-# INLINEABLE log1m #-}

-- vectorized log of real-valued binomial coefficient
-- see: https://mc-stan.org/docs/functions-reference/betafun.html
lChoose :: VectorizedReal t => Function t '[t, t]
lChoose = simpleFunction "lchoose"
{-# INLINEABLE lChoose #-}

inv :: VectorizedReal t => Function t '[t]
inv = simpleFunction "inv"
{-# INLINEABLE inv #-}

abs :: VectorizedReal t => Function t '[t]
abs = simpleFunction "abs"
{-# INLINEABLE abs #-}

mean :: (TypeOneOf t [ECVec, ERVec, EMat, ESqMat], GenSType t) => Function EReal '[t]
mean = simpleFunction "mean"
{-# INLINEABLE mean #-}

sd :: (TypeOneOf t [ECVec, ERVec, EMat, ESqMat], GenSType t) => Function EReal '[t]
sd = simpleFunction "sd"
{-# INLINEABLE sd #-}

variance :: (TypeOneOf t [ECVec, ERVec, EMat, ESqMat], GenSType t) => Function EReal '[t]
variance = simpleFunction "variance"
{-# INLINEABLE variance #-}

targetVal :: Function EReal '[]
targetVal = simpleFunction "target"
{-# INLINEABLE targetVal #-}

array_num_elements :: (SNatI n, GenSType t) => Function EInt '[EArray n t]
array_num_elements = simpleFunction "inv"
{-# INLINEABLE array_num_elements #-}

to_vector :: (TypeOneOf t [ECVec, ERVec, EArray1 EInt, EArray1 EReal, EMat, ESqMat], GenSType t)
          => Function ECVec '[t]
to_vector = simpleFunction "to_vector"
{-# INLINEABLE to_vector #-}

toVec :: (TypeOneOf t [ECVec, ERVec, EArray1 EInt, EArray1 EReal, EMat, ESqMat], GenSType t)
          => UExpr t -> UExpr ECVec
toVec x = functionE to_vector (x :> TNil)
{-# INLINEABLE toVec #-}

to_row_vector :: (TypeOneOf t [ECVec, ERVec, EArray1 EInt, EArray1 EReal, EMat, ESqMat], GenSType t)
          => Function ERVec '[t]
to_row_vector = simpleFunction "to_row_vector"
{-# INLINEABLE to_row_vector #-}

size :: (IsContainer t, GenSType t) => Function EInt '[t]
size = simpleFunction "size"
{-# INLINEABLE size #-}

sum :: (TypeOneOf t '[ECVec, ERVec, EMat, ESqMat, ERealArray], GenSType t) => Function EReal '[t]
sum = simpleFunction "sum"
{-# INLINEABLE sum #-}

sumInt :: Function EInt '[EIntArray]
sumInt = simpleFunction "sum"
{-# INLINEABLE sumInt #-}

rep_vector :: Function ECVec '[EReal, EInt]
rep_vector = simpleFunction "rep_vector"
{-# INLINEABLE rep_vector #-}

rep_row_vector :: Function ERVec '[EReal, EInt]
rep_row_vector = simpleFunction "rep_row_vector"
{-# INLINEABLE rep_row_vector #-}

ones_vector :: Function ECVec '[EInt]
ones_vector = simpleFunction "ones_vector"
{-# INLINEABLE ones_vector #-}

ones_row_vector :: Function ERVec '[EInt]
ones_row_vector = simpleFunction "ones_row_vector"
{-# INLINEABLE ones_row_vector #-}

{-
type family NInts (n :: Nat) :: [EType] where
  NInts Z = '[]
  NInts (S n) = EInt ': NInts n

rep_array :: (GenSType t, GenTypeList (NInts n), SNatI n) => Function (EArray n t) (t ': NInts n)
rep_array = simpleFunction "rep_array"
{-# INLINEABLE rep_array #-}


-}
-- this pleases me
rep_array :: (GenSType t, GenTypeList (SameTypeList EInt n), SNatI n) => Function (EArray n t) (t ': SameTypeList EInt n)
rep_array = simpleFunction "rep_array"
{-# INLINEABLE rep_array #-}

dot_product :: (TypeOneOf t '[ECVec, ERVec], GenSType t, TypeOneOf t' '[ECVec, ERVec], GenSType t')
            => Function EReal '[t, t']
dot_product = simpleFunction "dot_product"
{-# INLINEABLE dot_product #-}

type family RepArgs (t :: EType) :: [EType] where
  RepArgs ECVec = [EReal, EInt]
  RepArgs ERVec = [EReal, EInt]
  RepArgs EMat = [EReal, EInt, EInt]
--  RepArgs ESqMat = [EReal, EInt]
  RepArgs t = TE.TypeError (TE.Text "Cannot fill " :<>: TE.ShowType t :<>: TE.Text " like a container (e.g., vector, matrix)")

-- this might not be so useful because GHC/Haskell cannot neccessarily see through the constraints
rep_container :: (TypeOneOf t '[ECVec, EMat]) => SType t -> Function t (RepArgs t)
rep_container st = case st of
  SCVec -> rep_vector
  SMat -> rep_matrix
--  SSqMat -> rep_sq_matrix
{-# INLINEABLE rep_container #-}

rep_matrix :: Function EMat '[EReal, EInt, EInt]
rep_matrix = simpleFunction "rep_matrix"
{-# INLINEABLE rep_matrix #-}

repV_matrix :: (TypeOneOf t '[ECVec, ERVec], GenSType t) => Function EMat '[t, EInt]
repV_matrix = simpleFunction "rep_matrix"
{-# INLINEABLE repV_matrix #-}

{-
rep_sq_matrix :: Function ESqMat '[EReal, EInt]
rep_sq_matrix = Function "rep_matrix" SSqMat (SReal ::> SInt ::> TypeNil) f
  where
    f :: TypedList u '[EReal, EInt] -> TypedList u '[EReal, EInt, EInt]
    f (a :> b :> TNil) = a :> b :> b :> TNil
{-# INLINEABLE rep_sq_matrix #-}
-}

vecArrayToMatrix :: (TypeOneOf t [ECVec, ERVec], GenSType t) => Function EMat '[EArray1 t]
vecArrayToMatrix = simpleFunction "to_matrix"
{-# INLINEABLE vecArrayToMatrix #-}

vecToMatrix :: (TypeOneOf t [ECVec, ERVec], GenSType t) => Function EMat '[t, EInt, EInt]
vecToMatrix = simpleFunction "to_matrix"
{-# INLINEABLE vecToMatrix #-}

type DiagMultiplyC t = (TypeOneOf t [EMat, ESqMat], GenSType t)

diagPreMultiply :: DiagMultiplyC t => Function t '[ERVec, t]
diagPreMultiply = simpleFunction "diag_pre_multiply"
{-# INLINEABLE diagPreMultiply #-}

diagPostMultiply :: DiagMultiplyC t => Function t '[t, ECVec]
diagPostMultiply = simpleFunction "diag_post_multiply"
{-# INLINEABLE diagPostMultiply #-}

quadFormDiag :: (DiagMultiplyC t, TypeOneOf t' [ECVec, ERVec], GenSType t') => Function t '[t, t']
quadFormDiag = simpleFunction "quad_form_diag"
{-# INLINEABLE quadFormDiag #-}


segment :: (IsContainer t, GenSType t) => Function t [t, EInt, EInt]
segment = simpleFunction "segment"
{-# INLINEABLE segment #-}

inverse :: (TypeOneOf t [EMat, ESqMat], GenSType t) => Function t '[t]
inverse = simpleFunction "inverse"
{-# INLINEABLE inverse #-}

qr_thin_Q :: Function EMat '[EMat]
qr_thin_Q = simpleFunction "qr_thin_Q"
{-# INLINEABLE qr_thin_Q #-}

qr_thin_R :: Function EMat '[EMat]
qr_thin_R = simpleFunction "qr_thin_R"
{-# INLINEABLE qr_thin_R #-}

block :: Function EMat [EMat, EInt, EInt, EInt, EInt]
block = simpleFunction "block"
{-# INLINEABLE block #-}

sub_col :: Function ECVec [EMat, EInt, EInt, EInt]
sub_col = simpleFunction "sub_col"
{-# INLINEABLE sub_col #-}

sub_row :: Function ERVec [EMat, EInt, EInt, EInt]
sub_row = simpleFunction "sub_row"
{-# INLINEABLE sub_row #-}

append_col :: Function EMat [EMat, ECVec]
append_col = simpleFunction "append_col"
{-# INLINEABLE append_col #-}

append_row :: Function EMat [EMat, ERVec]
append_row = simpleFunction "append_row"
{-# INLINEABLE append_row #-}

append_to_row_vector :: Function ERVec [ERVec, EReal]
append_to_row_vector = simpleFunction "append_col"
{-# INLINEABLE append_to_row_vector #-}

append_to_vector :: Function ECVec [ECVec, EReal]
append_to_vector = simpleFunction "append_row"
{-# INLINEABLE append_to_vector #-}


rows :: (TypeOneOf t [EMat, ESqMat], GenSType t) => Function EInt '[t]
rows = simpleFunction "rows"
{-# INLINEABLE rows #-}

cols :: (TypeOneOf t [EMat, ESqMat], GenSType t) => Function EInt '[t]
cols = simpleFunction "cols"
{-# INLINEABLE cols #-}

diagonal :: (TypeOneOf t [EMat, ESqMat], GenSType t) => Function ECVec '[t]
diagonal = simpleFunction "diagonal"
{-# INLINEABLE diagonal #-}

-- NB: Stan docs warn against using this because there's usually a more efficient option
-- But I'm not sure what to do with multiple draws from uncorrelated normals
diag_matrix :: (TypeOneOf t [ERVec, ECVec], GenSType t
--               ,TypeOneOf rt [EMat, ESqMat], GenSType rt
               ) => Function ESqMat '[t]
diag_matrix = simpleFunction "diag_matrix"
{-# INLINEABLE diag_matrix #-}

diag_pre_multiply :: (TypeOneOf t [ECVec, ERVec], GenSType t, TypeOneOf t' [EMat, ESqMat], GenSType t')
                  => Function t' [t, t']
diag_pre_multiply = simpleFunction "diag_pre_multiply"
{-# INLINEABLE diag_pre_multiply #-}

diag_post_multiply :: (TypeOneOf t [ECVec, ERVec], GenSType t, TypeOneOf t' [EMat, ESqMat], GenSType t')
                  => Function t' [t, t']
diag_post_multiply = simpleFunction "diag_post_multiply"
{-# INLINEABLE diag_post_multiply #-}

-- Densities & RNGs

uniform :: (TypeOneOf t [EReal, ECVec, ERVec], GenSType t) => Density t '[t, t]
uniform = simpleDensity "uniform"
{-# INLINEABLE uniform #-}

uniform_lpdf :: (TypeOneOf t [EReal, ECVec, ERVec], GenSType t) => Density t '[t, t]
uniform_lpdf = simpleDensity "uniform_lpdf"
{-# INLINEABLE uniform_lpdf #-}

uniform_lupdf :: (TypeOneOf t [EReal, ECVec, ERVec], GenSType t) => Density t '[t, t]
uniform_lupdf = simpleDensity "uniform_lupdf"
{-# INLINEABLE uniform_lupdf #-}

uniform_rng :: (TypeOneOf t [EReal, ECVec, ERVec], GenSType t) => Function t '[t, t]
uniform_rng = simpleFunction "uniform_rng"
{-# INLINEABLE uniform_rng #-}

normal :: (TypeOneOf t [EReal, ECVec, ERVec], GenSType t) => Density t '[t, t]
normal = simpleDensity "normal"
{-# INLINEABLE normal #-}

normal_lpdf :: (TypeOneOf t [EReal, ECVec, ERVec], GenSType t) => Density t '[t, t]
normal_lpdf = simpleDensity "normal_lpdf"
{-# INLINEABLE normal_lpdf #-}

normal_lupdf :: (TypeOneOf t [EReal, ECVec, ERVec], GenSType t) => Density t '[t, t]
normal_lupdf = simpleDensity "normal_lupdf"
{-# INLINEABLE normal_lupdf #-}

normal_rng :: (TypeOneOf t [EReal, ECVec, ERVec], GenSType t) => Function t '[t, t]
normal_rng = simpleFunction "normal_rng"
{-# INLINEABLE normal_rng #-}

normalS :: (TypeOneOf t [EReal, ECVec, ERVec], GenSType t) => Density t '[EReal, EReal]
normalS = simpleDensity "normal"
{-# INLINEABLE normalS #-}

normalS_lpdf :: (TypeOneOf t [EReal, ECVec, ERVec], GenSType t) => Density t '[EReal, EReal]
normalS_lpdf = simpleDensity "normal_lpdf"
{-# INLINEABLE normalS_lpdf #-}

normalS_lupdf :: (TypeOneOf t [EReal, ECVec, ERVec], GenSType t) => Density t '[EReal, EReal]
normalS_lupdf = simpleDensity "normal_lupdf"
{-# INLINEABLE normalS_lupdf #-}

normalS_rng :: (TypeOneOf t [EReal, ECVec, ERVec], GenSType t) => Function t '[EReal, EReal]
normalS_rng = simpleFunction "normal_rng"
{-# INLINEABLE normalS_rng #-}

std_normal :: (TypeOneOf t [EReal, ECVec, ERVec], GenSType t) => Density t '[]
std_normal = simpleDensity "std_normal"
{-# INLINEABLE std_normal #-}

std_normal_lpdf :: (TypeOneOf t [EReal, ECVec, ERVec], GenSType t) => Density t '[]
std_normal_lpdf = simpleDensity "std_normal_lpdf"
{-# INLINEABLE std_normal_lpdf #-}

std_normal_lupdf :: (TypeOneOf t [EReal, ECVec, ERVec], GenSType t) => Density t '[]
std_normal_lupdf = simpleDensity "std_normal_lupdf"
{-# INLINEABLE std_normal_lupdf #-}

std_normal_rng :: (TypeOneOf t [EReal, ECVec, ERVec], GenSType t) => Function t '[]
std_normal_rng = simpleFunction "std_normal_rng"
{-# INLINEABLE std_normal_rng #-}

lkj_corr_cholesky :: Density ESqMat '[EReal]
lkj_corr_cholesky = simpleDensity "lkj_corr_cholesky"
{-# INLINEABLE lkj_corr_cholesky #-}

type MultiNormalDensityC t = (TypeOneOf t [ECVec, ERVec, EArray1 ECVec, EArray1 ERVec], GenSType t)

-- the rng functions look like they return column vectors regardless of the input structure
type family MultiNormalRngReturnT t where
  MultiNormalRngReturnT ECVec = ECVec
  MultiNormalRngReturnT ERVec = ECVec
  MultiNormalRngReturnT (EArray1 ECVec) = EArray1 ECVec
  MultiNormalRngReturnT (EArray1 ERVec) = EArray1 ECVec


multi_normal_cholesky :: MultiNormalDensityC t => Density t '[t, ESqMat]
multi_normal_cholesky = simpleDensity "multi_normal_cholesky"
{-# INLINEABLE multi_normal_cholesky #-}

multi_normal_cholesky_lpdf :: MultiNormalDensityC t => Density t '[t, ESqMat]
multi_normal_cholesky_lpdf = simpleDensity "multi_normal_cholesky_lpdf"
{-# INLINEABLE multi_normal_cholesky_lpdf #-}

multi_normal_cholesky_lupdf :: MultiNormalDensityC t => Density t '[t, ESqMat]
multi_normal_cholesky_lupdf = simpleDensity "multi_normal_cholesky_lupdf"
{-# INLINEABLE multi_normal_cholesky_lupdf #-}

multi_normal_cholesky_rng :: (MultiNormalDensityC t, GenSType (MultiNormalRngReturnT t))
                          => Function (MultiNormalRngReturnT t) '[t, ESqMat]
multi_normal_cholesky_rng = simpleFunction "multi_normal_cholesky_rng"
{-# INLINEABLE multi_normal_cholesky_rng #-}

multi_normal :: MultiNormalDensityC t => Density t '[t, ESqMat]
multi_normal = simpleDensity "multi_normal"
{-# INLINEABLE multi_normal #-}

multi_normal_lpdf :: MultiNormalDensityC t => Density t '[t, ESqMat]
multi_normal_lpdf = simpleDensity "multi_normal_lpdf"
{-# INLINEABLE multi_normal_lpdf #-}

multi_normal_lupdf :: MultiNormalDensityC t => Density t '[t, ESqMat]
multi_normal_lupdf = simpleDensity "multi_normal_lupdf"
{-# INLINEABLE multi_normal_lupdf #-}

multi_normal_rng :: (MultiNormalDensityC t, GenSType (MultiNormalRngReturnT t))
                          => Function (MultiNormalRngReturnT t) '[t, ESqMat]
multi_normal_rng = simpleFunction "multi_normal_rng"
{-# INLINEABLE multi_normal_rng #-}


lognormal :: (TypeOneOf t [EReal, ECVec, ERVec], GenSType t) => Density t '[t, t]
lognormal = simpleDensity "lognormal"
{-# INLINEABLE lognormal #-}

lognormal_lpdf :: (TypeOneOf t [EReal, ECVec, ERVec], GenSType t) => Density t '[t, t]
lognormal_lpdf = simpleDensity "lognormal_lpdf"
{-# INLINEABLE lognormal_lpdf #-}

lognormal_lupdf :: (TypeOneOf t [EReal, ECVec, ERVec], GenSType t) => Density t '[t, t]
lognormal_lupdf = simpleDensity "lognormal_lupdf"
{-# INLINEABLE lognormal_lupdf #-}

lognormal_rng :: (TypeOneOf t [EReal, ECVec, ERVec], GenSType t) => Function t '[t, t]
lognormal_rng = simpleFunction "lognormal_rng"
{-# INLINEABLE lognormal_rng #-}

lognormalS :: (TypeOneOf t [EReal, ECVec, ERVec], GenSType t) => Density t '[EReal, EReal]
lognormalS = simpleDensity "lognormal"
{-# INLINEABLE lognormalS #-}

lognormalS_lpdf :: (TypeOneOf t [EReal, ECVec, ERVec], GenSType t) => Density t '[EReal, EReal]
lognormalS_lpdf = simpleDensity "lognormal_lpdf"
{-# INLINEABLE lognormalS_lpdf #-}

lognormalS_lupdf :: (TypeOneOf t [EReal, ECVec, ERVec], GenSType t) => Density t '[EReal, EReal]
lognormalS_lupdf = simpleDensity "lognormal_lupdf"
{-# INLINEABLE lognormalS_lupdf #-}

lognormalS_rng :: (TypeOneOf t [EReal, ECVec, ERVec], GenSType t) => Function t '[EReal, EReal]
lognormalS_rng = simpleFunction "lognormal_rng"
{-# INLINEABLE lognormalS_rng #-}

cauchy :: (TypeOneOf t [EReal, ECVec, ERVec], GenSType t) => Density t '[t, t]
cauchy = simpleDensity "cauchy"
{-# INLINEABLE cauchy #-}

cauchy_lpdf :: (TypeOneOf t [EReal, ECVec, ERVec], GenSType t) => Density t '[t, t]
cauchy_lpdf = simpleDensity "cauchy_lpdf"
{-# INLINEABLE cauchy_lpdf #-}

cauchy_lupdf :: (TypeOneOf t [EReal, ECVec, ERVec], GenSType t) => Density t '[t, t]
cauchy_lupdf = simpleDensity "cauchy_lupdf"
{-# INLINEABLE cauchy_lupdf #-}

cauchy_rng :: (TypeOneOf t [EReal, ECVec, ERVec], GenSType t) => Function t '[t, t]
cauchy_rng = simpleFunction "cauchy_rng"
{-# INLINEABLE cauchy_rng #-}

student_t :: (TypeOneOf t [EReal, ECVec, ERVec], GenSType t) => Density t '[t, t, t]
student_t = simpleDensity "student_t"
{-# INLINEABLE student_t #-}

student_t_lpdf :: (TypeOneOf t [EReal, ECVec, ERVec], GenSType t) => Density t '[t, t, t]
student_t_lpdf = simpleDensity "student_t_lpdf"
{-# INLINEABLE student_t_lpdf #-}

student_t_lupdf :: (TypeOneOf t [EReal, ECVec, ERVec], GenSType t) => Density t '[t, t, t]
student_t_lupdf = simpleDensity "student_t_lupdf"
{-# INLINEABLE student_t_lupdf #-}

student_t_rng :: (TypeOneOf t [EReal, ECVec, ERVec], GenSType t) => Function t '[t, t, t]
student_t_rng = simpleFunction "student_t_rng"
{-# INLINEABLE student_t_rng #-}

gamma :: (TypeOneOf t [EReal, ECVec, ERVec], GenSType t) => Density t '[t, t]
gamma = simpleDensity "gamma"
{-# INLINEABLE gamma #-}

gamma_lpdf :: (TypeOneOf t [EReal, ECVec, ERVec], GenSType t) => Density t '[t, t]
gamma_lpdf = simpleDensity "gammy_lpdf"
{-# INLINEABLE gamma_lpdf #-}

gamma_lupdf :: (TypeOneOf t [EReal, ECVec, ERVec], GenSType t) => Density t '[t, t]
gamma_lupdf = simpleDensity "gamma_lupdf"
{-# INLINEABLE gamma_lupdf #-}

gamma_rng :: (TypeOneOf t [EReal, ECVec, ERVec], GenSType t) => Function t '[t, t]
gamma_rng = simpleFunction "gamma_rng"
{-# INLINEABLE gamma_rng #-}





type BinDensityC t t' = (TypeOneOf t [EArray1 EInt, EInt], GenSType t
                        , TypeOneOf t' [EArray1 EReal, ECVec, EReal], ScalarType t' ~ EReal, GenSType t'
                        , Dimension t ~ Dimension t')

binomial :: BinDensityC t t' => Density t '[t, t']
binomial = simpleDensity "binomial"
{-# INLINEABLE binomial #-}

binomial_lpmf :: BinDensityC t t' => Density t '[t, t']
binomial_lpmf = simpleDensity "binomial_lpmf"
{-# INLINEABLE binomial_lpmf #-}

binomial_lupmf :: BinDensityC t t' => Density t '[t, t']
binomial_lupmf = simpleDensity "binomial_lupmf"
{-# INLINEABLE binomial_lupmf #-}

binomial_rng ::BinDensityC t t' => Function t '[t, t']
binomial_rng = simpleFunction "binomial_rng"
{-# INLINEABLE binomial_rng #-}

binomial_logit :: BinDensityC t t' => Density t '[t, t']
binomial_logit = simpleDensity "binomial_logit"
{-# INLINEABLE binomial_logit #-}

binomial_logit_lpmf :: BinDensityC t t' => Density t '[t, t']
binomial_logit_lpmf = simpleDensity "binomial_logit_lpmf"
{-# INLINEABLE binomial_logit_lpmf #-}

binomial_logit_lupmf :: BinDensityC t t' => Density t '[t, t']
binomial_logit_lupmf = simpleDensity "binomial_logit_lupmf"
{-# INLINEABLE binomial_logit_lupmf #-}

beta :: (VectorizedReal t, GenSType t) => Density t '[t, t]
beta = simpleDensity "beta"
{-# INLINEABLE beta #-}

beta_lpdf :: (VectorizedReal t, GenSType t) => Density t '[t, t]
beta_lpdf = simpleDensity "beta_lpdf"
{-# INLINEABLE beta_lpdf #-}

beta_lupdf :: (VectorizedReal t, GenSType t) => Density t '[t, t]
beta_lupdf = simpleDensity "beta_lupdf"
{-# INLINEABLE beta_lupdf #-}

beta_rng :: (VectorizedReal t, GenSType t) => Function t '[t, t]
beta_rng = simpleFunction "beta_rng"
{-# INLINEABLE beta_rng #-}

betaS :: (TypeOneOf t [EReal, ECVec, ERVec], GenSType t) => Density t '[EReal, EReal]
betaS = simpleDensity "beta"
{-# INLINEABLE betaS #-}

betaS_lpdf :: (TypeOneOf t [EReal, ECVec, ERVec], GenSType t) => Density t '[EReal, EReal]
betaS_lpdf = simpleDensity "beta_lpdf"
{-# INLINEABLE betaS_lpdf #-}

betaS_lupdf :: (TypeOneOf t [EReal, ECVec, ERVec], GenSType t) => Density t '[EReal, EReal]
betaS_lupdf = simpleDensity "beta_lupdf"
{-# INLINEABLE betaS_lupdf #-}

betaS_rng :: (TypeOneOf t [EReal, ECVec, ERVec], GenSType t) => Function t '[EReal, EReal]
betaS_rng = simpleFunction "beta_rng"
{-# INLINEABLE betaS_rng #-}



beta_proportion ::  (TypeOneOf t [EReal, ECVec], GenSType t) => Density t '[t, t]
beta_proportion = simpleDensity "beta_proportion"
{-# INLINEABLE beta_proportion #-}

beta_proportion_lpdf :: (TypeOneOf t [EReal, ECVec], GenSType t) => Density t '[t, t]
beta_proportion_lpdf = simpleDensity "beta_proportion_lpdf"
{-# INLINEABLE beta_proportion_lpdf #-}

beta_proportion_lupdf ::  (TypeOneOf t [EReal, ECVec], GenSType t) => Density t '[t, t]
beta_proportion_lupdf = simpleDensity "beta_proportion_lupdf"
{-# INLINEABLE beta_proportion_lupdf #-}

beta_proportion_rng ::  (TypeOneOf t [EReal, ECVec], GenSType t) => Function t '[t, t]
beta_proportion_rng = simpleFunction "beta_proportion_rng"
{-# INLINEABLE beta_proportion_rng #-}

beta_binomial :: BinDensityC t t' => Density t '[t, t', t']
beta_binomial = simpleDensity "beta_binomial"
{-# INLINEABLE beta_binomial #-}

beta_binomial_lpmf :: BinDensityC t t' => Density t '[t, t', t']
beta_binomial_lpmf = simpleDensity "beta_binomial_lpmf"
{-# INLINEABLE beta_binomial_lpmf #-}

beta_binomial_lupmf :: BinDensityC t t' => Density t '[t, t', t']
beta_binomial_lupmf = simpleDensity "beta_binomial_lupmf"
{-# INLINEABLE beta_binomial_lupmf #-}

beta_binomial_rng :: BinDensityC t t' => Function t '[t, t', t']
beta_binomial_rng = simpleFunction "beta_binomial_rng"
{-# INLINEABLE beta_binomial_rng #-}

-- softmax
softmax :: (TypeOneOf t [ECVec, ERVec], GenSType t) => Function t '[t]
softmax = simpleFunction "softmax"
{-# INLINEABLE softmax #-}

log_softmax :: (TypeOneOf t [ECVec, ERVec], GenSType t) => Function t '[t]
log_softmax = simpleFunction "log_softmax"
{-# INLINEABLE log_softmax #-}

-- Categorical
type CategoricalTypes t t' = (TypeOneOf t [EInt, EIntArray], GenSType t
                             , TypeOneOf t' [ESimplex, ECVec], GenSType t')
categorical :: CategoricalTypes t t' => Density t '[t']
categorical = simpleDensity "categorical"
{-# INLINEABLE categorical #-}

categorical_lpmf :: CategoricalTypes t t' => Density t '[t']
categorical_lpmf = simpleDensity "categorical_lpmf"
{-# INLINEABLE categorical_lpmf #-}

categorical_lupmf :: CategoricalTypes t t' => Density t '[t']
categorical_lupmf = simpleDensity "categorical_lupmf"
{-# INLINEABLE categorical_lupmf #-}

categorical_rng :: (TypeOneOf t [ESimplex, ECVec], GenSType t)  => Function EInt '[t]
categorical_rng = simpleFunction "categorical_rng"
{-# INLINEABLE categorical_rng #-}

categorical_logit :: (TypeOneOf t [EInt, EIntArray], GenSType t) => Density t '[ECVec]
categorical_logit = simpleDensity "categorical_logit"
{-# INLINEABLE categorical_logit #-}

categorical_logit_lpmf :: (TypeOneOf t [EInt, EIntArray], GenSType t) => Density t '[ECVec]
categorical_logit_lpmf = simpleDensity "categorical_logit_lpmf"
{-# INLINEABLE categorical_logit_lpmf #-}

categorical_logit_lupmf :: (TypeOneOf t [EInt, EIntArray], GenSType t) => Density t '[ECVec]
categorical_logit_lupmf = simpleDensity "categorical_logit_lupmf"
{-# INLINEABLE categorical_logit_lupmf #-}

categorical_logit_rng :: Function EInt '[ECVec]
categorical_logit_rng = simpleFunction "categorical_logit_lupmf"
{-# INLINEABLE categorical_logit_rng #-}


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
