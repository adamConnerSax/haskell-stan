{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Stan.BuildingBlocks.Distributions
  (
    module Stan.BuildingBlocks.Distributions
  )
where

import Prelude hiding (All)

import qualified Stan.Language as SL
import qualified Stan.Language.Statement as SL
import Stan.Language (TypedList(..))
import Stan.Language.Recursion (hfmap)
import qualified Stan.Functions as SF
import Stan.Functions.Operators
import qualified Stan.Builder as SB
import qualified Stan.BuildingBlocks.ArrayHelpers as SBBA
import Data.Type.Equality ((:~:)(Refl),TestEquality(testEquality))

import Effectful (Eff)

data DistType = Discrete | Continuous deriving stock (Show, Eq)

data StanDist :: SL.EType -> [SL.EType] -> [SL.EType] -> Type where
  StanDist :: DistType
           -> (SL.UExpr t -> SL.ExprList ts -> SL.UStmt)
           -> (SL.UExpr t -> SL.ExprList ts -> SL.UExpr SL.EReal)
           -> (SL.UExpr t -> SL.ExprList ts -> SL.UExpr SL.EReal)
           -> (SL.ExprList rs -> SL.UExpr t)
           -> StanDist t ts rs

type SimpleDist t ts = StanDist t ts ts

distType :: StanDist t ts rs -> DistType
distType (StanDist t _ _ _ _) = t

familySample :: StanDist t ts rs -> SL.UExpr t -> SL.ExprList ts -> SL.UStmt
familySample (StanDist _ f _ _ _)  = f

familyLDF :: StanDist t ts rs -> SL.UExpr t -> SL.ExprList ts -> SL.UExpr SL.EReal
familyLDF (StanDist _ _ ldf _ _ ) = ldf

familyLUDF :: StanDist t ts rs -> SL.UExpr t -> SL.ExprList ts -> SL.UExpr SL.EReal
familyLUDF (StanDist _ _ _ ludf _ ) = ludf

familyRNG :: StanDist t ts rs -> SL.ExprList rs -> SL.UExpr t
familyRNG (StanDist _ _ _ _ rng ) = rng

applyToDist :: SL.UExpr x -> StanDist t (x ': xs) (x ': ys) -> StanDist t xs ys
applyToDist x (StanDist dt s ld lu rng) =
  StanDist dt
  (\t xs -> s t (x :> xs))
  (\t xs -> ld t (x :> xs))
  (\t xs -> lu t (x :> xs))
  (\rs -> rng (x :> rs))

sampleDistV :: SB.StanCodeC es => StanDist t args rargs -> SL.ExprList args -> SL.UExpr t -> Eff es ()
sampleDistV sDist args yV =  SB.inBlock SL.SBModel $ SB.addStmtToCode $ familySample sDist yV args

normalDist :: forall t.(SL.TypeOneOf t [SL.EReal, SL.ECVec, SL.ERVec], SL.GenSType t) => SimpleDist t '[t, t]
normalDist = StanDist Continuous sample lpdf lupdf rng
  where
    sample x = SL.sample x SF.normal
    lpdf = SL.densityE SF.normal_lpdf
    lupdf = SL.densityE SF.normal_lupdf
    rng (m :> s :> TNil) = case SL.genSType @t of
      SL.SReal -> SF.normal_rng m s
      SL.SCVec -> SF.to_vector (SF.normal_rng m s) -- why does the stan version return array[] real??
      SL.SRVec -> SF.to_row_vector $ SF.normal_rng m s -- why does the stan version return array[] real??

-- This might be sketchy! It imagines a (vector of) weight(s) coming only from repetition of the same observation
-- it divides the sigmas by the sqrt of the weights (which has the effect of multiplying the log-prob by the weight)
-- and multiplying the RNG result by the weight.
countScaledNormalDist :: forall t.(SL.TypeOneOf t [SL.EReal, SL.ECVec, SL.ERVec], SL.GenSType t) => SimpleDist t '[t, t, t]
countScaledNormalDist = StanDist Continuous sample lpdf lupdf rng
  where
--    eltDivide = SL.binaryOpE (SL.SElementWise SL.SDivide)
--    eltTimes = SL.binaryOpE (SL.SElementWise SL.SMultiply)
    f :: SL.UExpr t -> SL.UExpr t -> SL.UExpr t
    f x y = case SL.genSType @t of
      SL.SReal -> case testEquality (SL.genSType @t) (SL.genSType @SL.EReal)  of
        Just Refl -> x |/| SF.sqrt y
        _ -> error "The impossible happened in countScaledNormalDist" -- this case can't occur based on the constraint above
      SL.SCVec -> case testEquality (SL.genSType @t) (SL.genSType @SL.ECVec)  of
        Just Refl -> x |./| (SF.sqrt y)
        _ -> error "The impossible happened in countScaledNormalDist" -- this case can't occur based on the constraint above
      SL.SRVec -> case testEquality (SL.genSType @t) (SL.genSType @SL.ERVec)  of
        Just Refl -> x |./| (SF.sqrt y)
        _ -> error "The impossible happened in countScaledNormalDist" -- this case can't occur based on the constraint above

    sample x (c :> mu :> sigma :> TNil) = SL.sample x SF.normal (mu :> f sigma c :> TNil)
    lpdf x (c :> mu :> sigma :> TNil) = SL.densityE SF.normal_lpdf x (mu :> f sigma c :> TNil)
    lupdf x (c :> mu :> sigma :> TNil) = SL.densityE SF.normal_lupdf x (mu :> f sigma c :> TNil)
    rng (c :> m :> s :> TNil) = case SL.genSType @t of
      SL.SReal -> c |*| SF.normal_rng m s
      SL.SCVec -> c |.*| SF.to_vector (SF.normal_rng m s) -- why does the stan version return array[] real??
      SL.SRVec -> c |.*| SF.to_row_vector (SF.normal_rng m s) -- why does the stan version return array[] real??

scalarNormalDist :: forall t . (SL.TypeOneOf t [SL.EReal, SL.ECVec, SL.ERVec], SL.GenSType t) => SimpleDist t '[SL.EReal, SL.EReal]
scalarNormalDist = StanDist Continuous sample lpdf lupdf rng
  where
    sample x  = SL.sample x SF.normalS
    lpdf = SL.densityE SF.normalS_lpdf
    lupdf = SL.densityE SF.normalS_lupdf
    rng :: SL.ExprList [SL.EReal, SL.EReal] -> SL.UExpr t
    rng (m :> s :> TNil) = SF.normalS_rng m s

cauchyDist :: forall t.(SL.TypeOneOf t [SL.EReal, SL.ECVec, SL.ERVec], SL.GenSType t) => SimpleDist t '[t, t]
cauchyDist = StanDist Continuous sample lpdf lupdf rng
  where
    sample x = SL.sample x SF.cauchy
    lpdf = SL.densityE SF.cauchy_lpdf
    lupdf = SL.densityE SF.cauchy_lupdf
    rng (a :> b :> TNil) = case SL.genSType @t of
      SL.SReal -> SF.cauchy_rng a b
      SL.SCVec -> SF.to_vector (SF.cauchy_rng a b)
      SL.SRVec -> SF.to_row_vector (SF.cauchy_rng a b)

studentTDist :: forall t.(SL.TypeOneOf t [SL.EReal, SL.ECVec, SL.ERVec], SL.GenSType t) => SimpleDist t '[t, t, t]
studentTDist = StanDist Continuous sample lpdf lupdf rng
  where
    sample x = SL.sample x SF.student_t
    lpdf = SL.densityE SF.student_t_lpdf
    lupdf = SL.densityE SF.student_t_lupdf
    rng (a :> b :> c :> TNil) = case SL.genSType @t of
      SL.SReal -> SF.student_t_rng a b c
      SL.SCVec -> SF.to_vector (SF.student_t_rng a b c)
      SL.SRVec -> SF.to_row_vector (SF.student_t_rng a b c)

binomialDist' :: forall t t' . SF.BinDensityC t t' => Bool -> SimpleDist t '[t, t']
binomialDist' sampleWithConstants = StanDist Discrete sample lpmf lupmf rng
  where
    sample gE args = if sampleWithConstants
                     then SL.target $ SL.densityE SF.binomial_lpmf gE args
                     else SL.sample gE SF.binomial args
    lpmf = SL.densityE SF.binomial_lpmf
    lupmf = SL.densityE SF.binomial_lupmf
    rng :: SL.ExprList [t, t'] -> SL.UExpr t
    rng  (n :> p :> TNil) = SF.binomial_rng n p

binomialDist ::  SF.BinDensityC t t' => SimpleDist t '[t, t']
binomialDist = binomialDist' False

binomialLogitDist' :: SF.BinDensityC t t' => Bool -> SimpleDist t '[t, t']
binomialLogitDist' sampleWithConstants = StanDist Discrete sample lpmf lupmf rng
  where
    sample gE args = if sampleWithConstants
                     then SL.target $ SL.densityE SF.binomial_logit_lpmf gE args
                     else SL.sample gE SF.binomial_logit args
    lpmf = SL.densityE SF.binomial_logit_lpmf
    lupmf = SL.densityE SF.binomial_logit_lupmf
    rng :: SF.BinDensityC t t' => SL.ExprList [t, t'] -> SL.UExpr t
    rng (tE :> pE :> TNil)= SF.binomial_rng tE (SF.inv_logit pE)

binomialLogitDist :: SF.BinDensityC t t' => SimpleDist t '[t, t']
binomialLogitDist = binomialLogitDist' False

binomialLogitDistWithConstants ::  SF.BinDensityC t t' => SimpleDist t '[t, t']
binomialLogitDistWithConstants = binomialLogitDist' True

betaDist :: forall t . (SL.TypeOneOf t [SL.EReal, SL.ECVec, SL.ERVec], SL.GenSType t) => SimpleDist t '[t, t] --SimpleDist TE.EReal '[TE.EReal, TE.EReal]
betaDist = StanDist Continuous sample lpdf lupdf rng
  where
    sample x = SL.sample x SF.beta
    lpdf = SL.densityE SF.beta_lpdf
    lupdf = SL.densityE SF.beta_lupdf
    rng (a :> b :> TNil) = case SL.genSType @t of
      SL.SReal -> SF.beta_rng a b
      SL.SCVec -> SF.to_vector (SF.beta_rng a b)
      SL.SRVec -> SF.to_row_vector (SF.beta_rng a b)

-- given a (real) "count" n and probability p, log-likelihood, etc. of a given proportion theta
-- coming from beta(alpha, beta) where
-- alpha = np + 1
-- beta = n (1 - p)
countScaledBetaDist :: forall t . (SL.TypeOneOf t [SL.EReal, SL.ECVec, SL.ERVec], SL.GenSType t
                                  , SL.BinaryResultT (SL.BElementWise 'SL.BMultiply) t t ~ t
                                  )
                    => SimpleDist t '[t, t]
countScaledBetaDist = StanDist Continuous sample lpdf lupdf rng
  where
    ones :: SL.UExpr t -> SL.UExpr t
    ones x = case SL.genSType @t of
      SL.SCVec -> SF.ones_vector (SF.size x)
      SL.SRVec -> SF.ones_row_vector (SF.size x)
      SL.SReal -> SL.realE 1
    alpha n p = p |.*| n |+| ones n
    beta n p = (n |.*| (ones n |-| p)) |+| ones n
    sample t (n :> p :> TNil) = SL.sample t (SF.beta @t) (alpha n p :> beta n p :> TNil)
    lpdf t (n :> p :> TNil) = SL.densityE SF.beta_lpdf t (alpha n p :> beta n p :> TNil)
    lupdf t (n :> p :> TNil) = SL.densityE SF.beta_lupdf t (alpha n p :> beta n p :> TNil)
    rng (n :> p :> TNil) = (n |+| ones n) |.*| SF.beta_rng (alpha n p) (beta n p)

scalarCountScaledBetaDist :: SimpleDist SL.EReal '[SL.EReal, SL.EReal]
scalarCountScaledBetaDist = StanDist Continuous sample lpdf lupdf rng
  where
    alpha n p = p |*| n |+| SL.realE 1
    beta n p = n |*| (SL.realE 1 |-| p) |+| SL.realE 1
    sample :: SL.RealE -> SL.ExprList '[SL.EReal, SL.EReal] -> SL.UStmt
    sample t (n :> p :> TNil) = SL.sample t SF.betaS (alpha n p :> beta n p :> TNil)
    lpdf :: SL.RealE -> SL.ExprList '[SL.EReal, SL.EReal] -> SL.UExpr SL.EReal
    lpdf t (n :> p :> TNil) = SL.densityE SF.betaS_lpdf t (alpha n p :> beta n p :> TNil)
    lupdf :: SL.RealE -> SL.ExprList '[SL.EReal, SL.EReal] -> SL.UExpr SL.EReal
    lupdf t (n :> p :> TNil) = SL.densityE SF.betaS_lupdf t (alpha n p :> beta n p :> TNil)
    rng :: SL.ExprList '[SL.EReal, SL.EReal] -> SL.RealE
    rng (n :> p :> TNil) = (n |+| SL.realE 1) |*| SF.betaS_rng @SL.EReal (alpha n p) (beta n p)

countScaledBetaDistLogit :: forall t . (SL.TypeOneOf t [SL.EReal, SL.ECVec, SL.ERVec], SL.ScalarType t ~ SL.EReal
                                       , SL.GenSType t
                                       , SL.BinaryResultT (SL.BElementWise 'SL.BMultiply) t t ~ t
                                       )
                         => SimpleDist t '[t, t]
countScaledBetaDistLogit = StanDist Continuous sample lpdf lupdf rng
  where
    (StanDist _ sample' lpdf' lupdf' rng') = countScaledBetaDist
    sample t (n :> lp :> TNil) = sample' t (n :> SF.inv_logit lp :> TNil)
    lpdf t (n :> lp :> TNil) = lpdf' t (n :> SF.inv_logit lp :> TNil)
    lupdf t (n :> lp :> TNil) = lupdf' t (n :> SF.inv_logit lp :> TNil)
    rng (n :> lp :> TNil) = rng' (n :> SF.inv_logit lp :> TNil)

scalarCountScaledBetaDistLogit :: SimpleDist SL.EReal '[SL.EReal, SL.EReal]
scalarCountScaledBetaDistLogit = StanDist Continuous sample lpdf lupdf rng
  where
    (StanDist _ sample' lpdf' lupdf' rng') = scalarCountScaledBetaDist
    sample :: SL.RealE -> SL.ExprList '[SL.EReal, SL.EReal] -> SL.UStmt
    sample t (n :> lp :> TNil) = sample' t (n :> SF.inv_logit lp :> TNil)
    lpdf :: SL.RealE -> SL.ExprList '[SL.EReal, SL.EReal] -> SL.UExpr SL.EReal
    lpdf t (n :> lp :> TNil) = lpdf' t (n :> SF.inv_logit lp :> TNil)
    lupdf :: SL.RealE -> SL.ExprList '[SL.EReal, SL.EReal] -> SL.UExpr SL.EReal
    lupdf t (n :> lp :> TNil) = lupdf' t (n :> SF.inv_logit lp :> TNil)
    rng :: SL.ExprList '[SL.EReal, SL.EReal] -> SL.RealE
    rng (n :> lp :> TNil) = rng' (n :> SF.inv_logit lp :> TNil)

betaDistV :: forall t . (SL.TypeOneOf t [SL.EReal, SL.ECVec, SL.ERVec], SL.GenSType t) => SimpleDist t '[t, t]
betaDistV = StanDist Continuous sample lpdf lupdf rng
  where
    sample x = SL.sample x SF.beta
    lpdf = SL.densityE SF.beta_lpdf
    lupdf = SL.densityE SF.beta_lupdf
    rng :: SL.ExprList [t, t] -> SL.UExpr t
    rng (a :> b :> TNil) = SF.beta_rng a b

betaMu :: SL.UExpr SL.EReal -> SL.UExpr SL.EReal -> SL.UExpr SL.EReal
betaMu aE bE = aE |/| (aE |+| bE)

betaProportionDist :: forall t . (SL.TypeOneOf t [SL.EReal, SL.ECVec, SL.ERVec], SL.GenSType t) => SimpleDist t '[t, t]
betaProportionDist = StanDist Continuous sample lpdf lupdf rng
  where
    sample x = SL.sample x SF.beta_proportion
    lpdf = SL.densityE SF.beta_proportion_lpdf
    lupdf = SL.densityE SF.beta_proportion_lupdf
    rng (a :> b :> TNil) =  case SL.genSType @t of
      SL.SReal -> SF.beta_proportion_rng a b
      SL.SCVec -> SF.to_vector (SF.beta_proportion_rng a b)
      SL.SRVec -> SF.to_row_vector (SF.beta_proportion_rng a b)

realToSameSizeVec :: SL.UExpr (SL.EArray1 SL.EInt) -> SL.UExpr SL.EReal -> SL.UExpr SL.ECVec
realToSameSizeVec v x = SF.rep_vector x (SF.size v)

betaBinomialDist' :: forall t t' . SF.BinDensityC t t' => Bool -> SimpleDist t '[t, t',t']
betaBinomialDist' sampleWithConstants = StanDist Discrete sample lpmf lupmf rng
  where
    sample x args = if sampleWithConstants
                    then SL.target $ SL.densityE SF.beta_binomial_lpmf x args
                    else SL.sample x SF.beta_binomial args
    lpmf = SL.densityE SF.beta_binomial_lpmf
    lupmf = SL.densityE SF.beta_binomial_lupmf
    rng :: SL.ExprList [t, t', t'] -> SL.UExpr t
    rng (n :> a :> b :> TNil) = SF.beta_binomial_rng n a b

-- beta-binomial but with the same parameters for every row
scalarBetaBinomialDist' :: Bool -> SimpleDist (SL.EArray1 SL.EInt) '[SL.EArray1 SL.EInt, SL.EReal, SL.EReal]
scalarBetaBinomialDist' sampleWithConstants = StanDist Discrete sample lpmf lupmf rng
  where
    (StanDist _ sample' lpmf' lupmf' rng') = betaBinomialDist' @(SL.EArray1 SL.EInt) @SL.ECVec sampleWithConstants
    sample x  = sample' x . argsToVecs
    lpmf x = lpmf' x . argsToVecs
    lupmf x = lupmf' x . argsToVecs
    rng = rng' . argsToVecs

scaledIntVec :: SL.UExpr SL.EReal
             -> SL.UExpr (SL.EArray1 SL.EInt)
             -> SL.UExpr SL.ECVec
scaledIntVec x iv = x `SL.timesE` intsToVec iv

countScaledBetaBinomialDist :: forall t t'.(SF.BinDensityC t t'
                                           , SL.TypeOneOf t' '[SL.EReal, SL.ECVec])
                            => Bool -> SimpleDist t '[t, t', t']
countScaledBetaBinomialDist sampleWithConstants = StanDist Discrete sample lpmf lupmf rng
  where
    f :: SL.UExpr t' -> SL.UExpr t -> SL.UExpr t'
    f x = case SL.genSType @t' of
      SL.SCVec -> case testEquality (SL.genSType @t) (SL.genSType @(SL.EArray1 SL.EInt))  of
        Just Refl -> {- SL.binaryOpE (SL.SElementWise SL.SMultiply)-} (|.*|) x . intsToVec
        _ -> error "The impossible happened in countScaledBinomialDist" -- this case can't occur based on the constraint above
      SL.SReal -> case testEquality (SL.genSType @t) (SL.genSType @SL.EInt)  of
        Just Refl -> (|*|) x
        _ -> error "The impossible happened in countScaledBinomialDist" -- this case can't occur based on the constraint above
--    sample :: SL.UExpr (SL.EArray1 SL.EInt) -> SL.ExprList [SL.EArray1 SL.EInt, SL.ECVec, SL.ECVec] -> SL.UStmt
    sample x (t :> a :> b :> TNil) = if sampleWithConstants
                                     then SL.target $ SL.densityE SF.beta_binomial_lpmf x (t :> f a t :> f b t :> TNil)
                                     else SL.sample x SF.beta_binomial (t :> f a t :> f b t :> TNil)
--    lpmf :: SL.UExpr (SL.EArray1 SL.EInt) -> SL.ExprList '[SL.EArray1 SL.EInt, SL.ECVec, SL.ECVec] -> SL.UExpr SL.EReal
    lpmf x (t :> a :> b :> TNil)  = SL.densityE SF.beta_binomial_lpmf x (t :> f a t :> f b t :> TNil)
--    lupmf :: SL.UExpr (SL.EArray1 SL.EInt) -> SL.ExprList '[SL.EArray1 SL.EInt, SL.ECVec, SL.ECVec] -> SL.UExpr SL.EReal
    lupmf x (t :> a :> b :> TNil)  = SL.densityE SF.beta_binomial_lupmf x (t :> f a t :> f b t :> TNil)
--    rng :: SL.ExprList '[SL.EArray1 SL.EInt, SL.ECVec, SL.ECVec] -> SL.UExpr (SL.EArray1 SL.EInt)
    rng (t :> a :> b :> TNil)  = SF.beta_binomial_rng t (f a t) (f b t)

countScaledScalarBetaBinomialDist :: Bool -> SimpleDist (SL.EArray1 SL.EInt) '[SL.EArray1 SL.EInt, SL.EReal, SL.EReal]
countScaledScalarBetaBinomialDist sampleWithConstants = StanDist Discrete sample lpmf lupmf rng
  where
    (StanDist _ sample' lpmf' lupmf' rng') = countScaledBetaBinomialDist sampleWithConstants
    sample x  = sample' x . argsToVecs
    lpmf x = lpmf' x . argsToVecs
    lupmf x = lupmf' x . argsToVecs
    rng = rng' . argsToVecs

argsToVecs :: SL.ExprList [SL.EArray1 SL.EInt, SL.EReal, SL.EReal] -> SL.ExprList [SL.EArray1 SL.EInt, SL.ECVec, SL.ECVec]
argsToVecs (t :> a :> b :> TNil) = t :> realToSameSizeVec t a :> realToSameSizeVec t b :> TNil

intsToVec :: SL.UExpr (SL.EArray1 SL.EInt) -> SL.UExpr SL.ECVec
intsToVec x = SF.to_vector x

categoricalDist :: forall t . SF.CategoricalTypes t  => SimpleDist t '[SL.ECVec]
categoricalDist = StanDist Discrete sample lpmf lupmf rng
  where
    sample y = SL.sample y SF.categorical
    lpmf = SL.densityE SF.categorical_lpmf
    lupmf = SL.densityE SF.categorical_lupmf
    rng (v :> TNil) = case SL.genSType @t of
      SL.SInt -> SF.categorical_rng v
      _ -> error "categorical_rng is not vectorized. For a vector of results, call from a loop."

categoricalLogitDist :: forall t . (SL.TypeOneOf t [SL.EInt, SL.EIntArray], SL.GenSType t) => SimpleDist t '[SL.ECVec]
categoricalLogitDist = StanDist Discrete sample lpmf lupmf rng
  where
    sample y = SL.sample y SF.categorical_logit
    lpmf = SL.densityE SF.categorical_logit_lpmf
    lupmf = SL.densityE SF.categorical_logit_lupmf
    rng (v :> TNil) = case SL.genSType @t of
      SL.SInt -> SF.categorical_logit_rng v
      _ -> error "categorical_logit_rng is not vectorized. For a vector of results, call from a loop."

multinomialDist ::  forall t . (SL.TypeOneOf t [SL.ECVec, SL.ERVec], SL.GenSType t) => StanDist SL.EIntArray '[t] [t, SL.EInt]
multinomialDist = StanDist Discrete sample lpmf lupmf rng
  where
    sample y = SL.sample y SF.multinomial
    lpmf  = SL.densityE SF.multinomial_lpmf
    lupmf  = SL.densityE SF.multinomial_lupmf
    rng :: SL.ExprList [t, SL.EInt] -> SL.UExpr SL.EIntArray
    rng  (theta :> n :> TNil) = SF.multinomial_rng theta n

multinomialLogitDist :: StanDist SL.EIntArray '[SL.ECVec] '[SL.ECVec, SL.EInt]
multinomialLogitDist = StanDist Discrete sample lpmf lupmf rng
  where
    sample y = SL.sample y SF.multinomial_logit
    lpmf  = SL.densityE SF.multinomial_logit_lpmf
    lupmf  = SL.densityE SF.multinomial_logit_lupmf
    rng :: SL.ExprList [SL.ECVec, SL.EInt] -> SL.UExpr SL.EIntArray
    rng (theta :> n :> TNil) = SF.multinomial_logit_rng theta n

{-
normallyApproximatedBinomial :: StanDist (SL.EArray1 SL.EInt) '[SL.EArray1 SL.EInt, SL.EReal]
normallyApproximatedBinomial = StanDist Continuous sample lpdf lupdf rng
  where
    mu p t = p `SL.timesE` intsToVec t
--    sigma :: SL.UExpr SL.EReal -> SL.UExpr (SL.EArray1 SL.EInt) -> SL.UExpr SL.ECVec
    sigma p t = SL.functionE (SL.sqrt SL.SReal) (p `SL.timesE` (SL.realE 1 `SL.minusE` p) :> TNil) `SL.timesE` intsToVec t
    sample :: SL.UExpr (SL.EArray1 SL.EInt) -> SL.ExprList [SL.EArray1 SL.EInt, SL.EReal] -> SL.UStmt
    sample s (t :> p :> TNil) = SL.sample (intsToVec s) (SL.normalDensity SL.SCVec) (mu p t :> sigma p t :> TNil)
    lpdf :: SL.UExpr (SL.EArray1 SL.EInt) -> SL.ExprList [SL.EArray1 SL.EInt, SL.EReal] -> SL.UExpr SL.EReal
    lpdf s (t :> p :> TNil)  = SL.densityE (SL.normalLPDF SL.SCVec) (intsToVec t) (mu p t :> sigma p t :> TNil)
    lupdf :: SL.UExpr (SL.EArray1 SL.EInt) -> SL.ExprList [SL.EArray1 SL.EInt, SL.EReal] -> SL.UExpr SL.EReal
    lupdf s (t :> p :> TNil) = SL.densityE (SL.normalLUPDF SL.SCVec) (intsToVec t) (mu p t :> sigma p t :> TNil)
    rng ::  SL.ExprList [SL.EArray1 SL.EInt, SL.EReal] -> SL.UExpr SL.ECVec
    rng (t :> p :> TNil) = SL.functionE (SL.normalRNG SL.SCVec) (mu p t :> sigma p t > TNil)


normallyApproximatedBinomialLogit :: SME.StanVar -> StanDist SME.StanExpr
normallyApproximatedBinomialLogit tV = StanDist Continuous sample lpdf lupdf rng
  where
    pE lpE = invLogit lpE
    mu lpE = pE lpE `vecTimes` toVec tV
    sigma lpE = SL.functionE (SL.sqrt SL.SCVec) (one $ pE lpE `vecTimes` (SME.scalar "1" `SL.minusE` pE lpE) `vecTimes` toVec tV)
    sample lpE sV = toVec sV `SME.vectorSample` SME.function "normal" (mu lpE :| [sigma lpE])
    lpdf lpE sV = SME.functionWithGivens "normal_lpdf" (one $ toVec sV) (mu lpE :| [sigma lpE])
    lupdf lpE sV = SME.functionWithGivens "normal_lupdf" (one $ toVec sV) (mu lpE :| [sigma lpE])
    rng lpE = SME.function "normal_rng" (mu lpE :| [sigma lpE])
-}

--invLogit :: SME.StanExpr -> SME.StanExpr
--invLogit e = SME.function "inv_logit" (one e)

--    expectation (aE, bE) = aE `SME.divide` (SME.paren $ aE `SME.plus` bE)
{-
-- for priors
normal :: Maybe SME.StanExpr -> SME.StanExpr -> SME.StanExpr
normal mMean sigma = SME.function "normal" (mean :| [sigma]) where
  mean = fromMaybe (SME.scalar "0") mMean

stdNormal :: SME.StanExpr
stdNormal = SME.function "std_normal" (one $ SME.nullE) --normal Nothing (SME.scalar "1")

normalDist :: StanDist (SME.StanExpr, SME.StanExpr)
normalDist = StanDist Continuous sample lpdf lupdf rng
  where
    sample (mean, sigma) yV = SME.target `plusEq` SME.functionWithGivens "normal_lupdf" (one $ SME.var yV) (mean :| [sigma])
    lpdf (mean, sigma) yV = SME.functionWithGivens "normal_lpdf" (one $ SME.var yV) (mean :| [sigma])
    lupdf (mean, sigma) yV = SME.functionWithGivens "normal_lupdf" (one $ SME.var yV) (mean :| [sigma])
    rng (mean, sigma) = SME.function "normal_rng" (mean :| [sigma])
--  expectation (mean, _) = mean

cauchy :: Maybe SME.StanExpr -> SME.StanExpr -> SME.StanExpr
cauchy mMean sigma = SME.function "cauchy" (mean :| [sigma]) where
  mean = fromMaybe (SME.scalar "0") mMean

gamma :: SME.StanExpr -> SME.StanExpr -> SME.StanExpr
gamma alpha beta = SME.function "gamma" (alpha :| [beta])
-}
