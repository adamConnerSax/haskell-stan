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

module Stan.ModelBuilder.Distributions
  (
    module Stan.ModelBuilder.Distributions
  )
where

--import Stan.ModelBuilder.Expressions as SME
import qualified Stan.ModelBuilder.TypedExpressions.Types as TE
import Stan.ModelBuilder.TypedExpressions.TypedList (TypedList(..))
import qualified Stan.ModelBuilder.TypedExpressions.Expressions as TE
import qualified Stan.ModelBuilder.TypedExpressions.Statements as TE
import qualified Stan.ModelBuilder.TypedExpressions.StanFunctions as TE
import Data.Type.Equality ((:~:)(Refl),TestEquality(testEquality))

import Prelude hiding (All)
import qualified Stan.ModelBuilder.TypedExpressions.Operations as TE

data DistType = Discrete | Continuous deriving stock (Show, Eq)

data StanDist :: TE.EType -> [TE.EType] -> [TE.EType] -> Type where
  StanDist :: DistType
           -> (TE.UExpr t -> TE.ExprList ts -> TE.UStmt)
           -> (TE.UExpr t -> TE.ExprList ts -> TE.UExpr TE.EReal)
           -> (TE.UExpr t -> TE.ExprList ts -> TE.UExpr TE.EReal)
           -> (TE.ExprList rs -> TE.UExpr t)
           -> StanDist t ts rs

type SimpleDist t ts = StanDist t ts ts

distType :: StanDist t ts rs -> DistType
distType (StanDist t _ _ _ _) = t

familySample :: StanDist t ts rs -> TE.UExpr t -> TE.ExprList ts -> TE.UStmt
familySample (StanDist _ f _ _ _)  = f

familyLDF :: StanDist t ts rs -> TE.UExpr t -> TE.ExprList ts -> TE.UExpr TE.EReal
familyLDF (StanDist _ _ ldf _ _ ) = ldf

familyLUDF :: StanDist t ts rs -> TE.UExpr t -> TE.ExprList ts -> TE.UExpr TE.EReal
familyLUDF (StanDist _ _ _ ludf _ ) = ludf

familyRNG :: StanDist t ts rs -> TE.ExprList rs -> TE.UExpr t
familyRNG (StanDist _ _ _ _ rng ) = rng

applyToDist :: TE.UExpr x -> StanDist t (x ': xs) (x ': ys) -> StanDist t xs ys
applyToDist x (StanDist dt s ld lu rng) =
  StanDist dt
  (\t xs -> s t (x :> xs))
  (\t xs -> ld t (x :> xs))
  (\t xs -> lu t (x :> xs))
  (\rs -> rng (x :> rs))

normalDist :: forall t.(TE.TypeOneOf t [TE.EReal, TE.ECVec, TE.ERVec], TE.GenSType t) => SimpleDist t '[t, t]
normalDist = StanDist Continuous sample lpdf lupdf rng
  where
    sample x = TE.sample x TE.normal
    lpdf = TE.densityE TE.normal_lpdf
    lupdf = TE.densityE TE.normal_lupdf
    rng ps = case TE.genSType @t of
      TE.SReal -> TE.functionE TE.normal_rng ps
      TE.SCVec -> TE.functionE TE.to_vector (TE.functionE TE.normal_rng ps :> TNil) -- why does the stan version return array[] real??
      TE.SRVec -> TE.functionE TE.to_row_vector (TE.functionE TE.normal_rng ps :> TNil) -- why does the stan version return array[] real??

-- This might be sketchy! It imagines a (vector of) weight(s) coming only from repetition of the same observation
-- it divides the sigmas by the sqrt of the weights (which has the effect of multiplying the log-prob by the weight)
-- and multiplying the RNG result by the weight.
countScaledNormalDist :: forall t.(TE.TypeOneOf t [TE.EReal, TE.ECVec, TE.ERVec], TE.GenSType t) => SimpleDist t '[t, t, t]
countScaledNormalDist = StanDist Continuous sample lpdf lupdf rng
  where
    eltDivide = TE.binaryOpE (TE.SElementWise TE.SDivide)
    eltTimes = TE.binaryOpE (TE.SElementWise TE.SMultiply)
    sqrtE x = TE.functionE TE.sqrt (x :> TNil)
    f :: TE.UExpr t -> TE.UExpr t -> TE.UExpr t
    f x y = case TE.genSType @t of
      TE.SReal -> case testEquality (TE.genSType @t) (TE.genSType @TE.EReal)  of
        Just Refl -> x `TE.divideE` sqrtE y
        _ -> error "The impossible happened in countScaledNormalDist" -- this case can't occur based on the constraint above
      TE.SCVec -> case testEquality (TE.genSType @t) (TE.genSType @TE.ECVec)  of
        Just Refl -> eltDivide x (sqrtE y)
        _ -> error "The impossible happened in countScaledNormalDist" -- this case can't occur based on the constraint above
      TE.SRVec -> case testEquality (TE.genSType @t) (TE.genSType @TE.ERVec)  of
        Just Refl -> eltDivide x (sqrtE y)
        _ -> error "The impossible happened in countScaledNormalDist" -- this case can't occur based on the constraint above

    sample x (c :> mu :> sigma :> TNil) = TE.sample x TE.normal (mu :> f sigma c :> TNil)
    lpdf x (c :> mu :> sigma :> TNil) = TE.densityE TE.normal_lpdf x (mu :> f sigma c :> TNil)
    lupdf x (c :> mu :> sigma :> TNil) = TE.densityE TE.normal_lupdf x (mu :> f sigma c :> TNil)
    rng (c :> ps) = case TE.genSType @t of
      TE.SReal -> c `TE.timesE` TE.functionE TE.normal_rng ps
      TE.SCVec -> c `eltTimes` TE.functionE TE.to_vector (TE.functionE TE.normal_rng ps :> TNil) -- why does the stan version return array[] real??
      TE.SRVec -> c `eltTimes` TE.functionE TE.to_row_vector (TE.functionE TE.normal_rng ps :> TNil) -- why does the stan version return array[] real??



scalarNormalDist :: (TE.TypeOneOf t [TE.EReal, TE.ECVec, TE.ERVec], TE.GenSType t) => SimpleDist t '[TE.EReal, TE.EReal]
scalarNormalDist = StanDist Continuous sample lpdf lupdf rng
  where
    sample x  = TE.sample x TE.normalS
    lpdf = TE.densityE TE.normalS_lpdf
    lupdf = TE.densityE TE.normalS_lupdf
    rng = TE.functionE TE.normalS_rng

cauchyDist :: forall t.(TE.TypeOneOf t [TE.EReal, TE.ECVec, TE.ERVec], TE.GenSType t) => SimpleDist t '[t, t]
cauchyDist = StanDist Continuous sample lpdf lupdf rng
  where
    sample x = TE.sample x TE.cauchy
    lpdf = TE.densityE TE.cauchy_lpdf
    lupdf = TE.densityE TE.cauchy_lupdf
    rng ps = case TE.genSType @t of
      TE.SReal -> TE.functionE TE.cauchy_rng ps
      TE.SCVec -> TE.functionE TE.to_vector (TE.functionE TE.cauchy_rng ps :> TNil)
      TE.SRVec -> TE.functionE TE.to_row_vector (TE.functionE TE.cauchy_rng ps :> TNil)


studentTDist :: forall t.(TE.TypeOneOf t [TE.EReal, TE.ECVec, TE.ERVec], TE.GenSType t) => SimpleDist t '[t, t, t]
studentTDist = StanDist Continuous sample lpdf lupdf rng
  where
    sample x = TE.sample x TE.student_t
    lpdf = TE.densityE TE.student_t_lpdf
    lupdf = TE.densityE TE.student_t_lupdf
    rng ps = case TE.genSType @t of
      TE.SReal -> TE.functionE TE.student_t_rng ps
      TE.SCVec -> TE.functionE TE.to_vector (TE.functionE TE.student_t_rng ps :> TNil)
      TE.SRVec -> TE.functionE TE.to_row_vector (TE.functionE TE.student_t_rng ps :> TNil)

binomialDist' :: TE.BinDensityC t t' => Bool -> SimpleDist t '[t, t']
binomialDist' sampleWithConstants = StanDist Discrete sample lpmf lupmf rng
  where
    sample gE args = if sampleWithConstants
                     then TE.target $ TE.densityE TE.binomial_lpmf gE args
                     else TE.sample gE TE.binomial args
    lpmf = TE.densityE TE.binomial_lpmf
    lupmf = TE.densityE TE.binomial_lupmf
    rng = TE.functionE TE.binomial_rng

binomialDist ::  TE.BinDensityC t t' => SimpleDist t '[t, t']
binomialDist = binomialDist' False

binomialLogitDist' :: TE.BinDensityC t t' => Bool -> SimpleDist t '[t, t']
binomialLogitDist' sampleWithConstants = StanDist Discrete sample lpmf lupmf rng
  where
    sample gE args = if sampleWithConstants
                     then TE.target $ TE.densityE TE.binomial_logit_lpmf gE args
                     else TE.sample gE TE.binomial_logit args
    lpmf = TE.densityE TE.binomial_logit_lpmf
    lupmf = TE.densityE TE.binomial_logit_lupmf
    rng :: TE.BinDensityC t t' => TE.ExprList [t, t'] -> TE.UExpr t
    rng (tE :> pE :> TNil)= TE.functionE TE.binomial_rng (tE :> TE.functionE TE.inv_logit (pE :> TNil) :> TNil)


binomialLogitDist :: TE.BinDensityC t t' => SimpleDist t '[t, t']
binomialLogitDist = binomialLogitDist' False

binomialLogitDistWithConstants ::  TE.BinDensityC t t' => SimpleDist t '[t, t']
binomialLogitDistWithConstants = binomialLogitDist' True


--vecTimes = TE.binaryOpE (TE.SElementWise TE.SMultiply)
--vecDivide = TE.binaryOpE (TE.SElementWise TE.SDivide)

betaDist :: SimpleDist TE.EReal '[TE.EReal, TE.EReal]
betaDist = StanDist Continuous sample lpdf lupdf rng
  where
    sample x = TE.sample x TE.beta
    lpdf = TE.densityE TE.beta_lpdf
    lupdf = TE.densityE TE.beta_lupdf
    rng = TE.functionE TE.beta_rng

betaMu :: TE.UExpr TE.EReal -> TE.UExpr TE.EReal -> TE.UExpr TE.EReal
betaMu aE bE = aE `TE.divideE` (aE `TE.plusE` bE)

betaProportionDist :: SimpleDist TE.EReal '[TE.EReal, TE.EReal]
betaProportionDist = StanDist Continuous sample lpdf lupdf rng
  where
    sample x = TE.sample x TE.beta_proportion
    lpdf = TE.densityE TE.beta_proportion_lpdf
    lupdf = TE.densityE TE.beta_proportion_lupdf
    rng = TE.functionE TE.beta_proportion_rng

realToSameSizeVec :: TE.UExpr (TE.EArray1 TE.EInt) -> TE.UExpr TE.EReal -> TE.UExpr TE.ECVec
realToSameSizeVec v x = TE.functionE TE.rep_vector (x :> TE.functionE TE.size (v :> TNil) :> TNil)

betaBinomialDist' :: forall t t'.TE.BinDensityC t t' => Bool -> SimpleDist t '[t, t',t']
betaBinomialDist' sampleWithConstants = StanDist Discrete sample lpmf lupmf rng
  where
    sample x args = if sampleWithConstants
                    then TE.target $ TE.densityE TE.beta_binomial_lpmf x args
                    else TE.sample x TE.beta_binomial args
    lpmf = TE.densityE TE.beta_binomial_lpmf
    lupmf = TE.densityE TE.beta_binomial_lupmf
    rng = TE.functionE TE.beta_binomial_rng

-- beta-binomial but with the same parameters for every row
scalarBetaBinomialDist' :: Bool -> SimpleDist (TE.EArray1 TE.EInt) '[TE.EArray1 TE.EInt, TE.EReal, TE.EReal]
scalarBetaBinomialDist' sampleWithConstants = StanDist Discrete sample lpmf lupmf rng
  where
    (StanDist _ sample' lpmf' lupmf' rng') = betaBinomialDist' @(TE.EArray1 TE.EInt) @TE.ECVec sampleWithConstants
    sample x  = sample' x . argsToVecs
    lpmf x = lpmf' x . argsToVecs
    lupmf x = lupmf' x . argsToVecs
    rng = rng' . argsToVecs

scaledIntVec :: TE.UExpr TE.EReal
             -> TE.UExpr (TE.EArray1 TE.EInt)
             -> TE.UExpr TE.ECVec
scaledIntVec x iv = x `TE.timesE` intsToVec iv

countScaledBetaBinomialDist :: forall t t'.(TE.BinDensityC t t'
                                           , TE.TypeOneOf t' '[TE.EReal, TE.ECVec])
                            => Bool -> SimpleDist t '[t, t', t']
countScaledBetaBinomialDist sampleWithConstants = StanDist Discrete sample lpmf lupmf rng
  where
    f :: TE.UExpr t' -> TE.UExpr t -> TE.UExpr t'
    f x = case TE.genSType @t' of
      TE.SCVec -> case testEquality (TE.genSType @t) (TE.genSType @(TE.EArray1 TE.EInt))  of
        Just Refl -> TE.binaryOpE (TE.SElementWise TE.SMultiply) x . intsToVec
        _ -> error "The impossible happened in countScaledBinomialDist" -- this case can't occur based on the constraint above
      TE.SReal -> case testEquality (TE.genSType @t) (TE.genSType @TE.EInt)  of
        Just Refl -> TE.timesE x
        _ -> error "The impossible happened in countScaledBinomialDist" -- this case can't occur based on the constraint above
--    sample :: TE.UExpr (TE.EArray1 TE.EInt) -> TE.ExprList [TE.EArray1 TE.EInt, TE.ECVec, TE.ECVec] -> TE.UStmt
    sample x (t :> a :> b :> TNil) = if sampleWithConstants
                                     then TE.target $ TE.densityE TE.beta_binomial_lpmf x (t :> f a t :> f b t :> TNil)
                                     else TE.sample x TE.beta_binomial (t :> f a t :> f b t :> TNil)
--    lpmf :: TE.UExpr (TE.EArray1 TE.EInt) -> TE.ExprList '[TE.EArray1 TE.EInt, TE.ECVec, TE.ECVec] -> TE.UExpr TE.EReal
    lpmf x (t :> a :> b :> TNil)  = TE.densityE TE.beta_binomial_lpmf x (t :> f a t :> f b t :> TNil)
--    lupmf :: TE.UExpr (TE.EArray1 TE.EInt) -> TE.ExprList '[TE.EArray1 TE.EInt, TE.ECVec, TE.ECVec] -> TE.UExpr TE.EReal
    lupmf x (t :> a :> b :> TNil)  = TE.densityE TE.beta_binomial_lupmf x (t :> f a t :> f b t :> TNil)
--    rng :: TE.ExprList '[TE.EArray1 TE.EInt, TE.ECVec, TE.ECVec] -> TE.UExpr (TE.EArray1 TE.EInt)
    rng (t :> a :> b :> TNil)  = TE.functionE TE.beta_binomial_rng (t :> f a t :> f b t :> TNil)

countScaledScalarBetaBinomialDist :: Bool -> SimpleDist (TE.EArray1 TE.EInt) '[TE.EArray1 TE.EInt, TE.EReal, TE.EReal]
countScaledScalarBetaBinomialDist sampleWithConstants = StanDist Discrete sample lpmf lupmf rng
  where
    (StanDist _ sample' lpmf' lupmf' rng') = countScaledBetaBinomialDist sampleWithConstants
    sample x  = sample' x . argsToVecs
    lpmf x = lpmf' x . argsToVecs
    lupmf x = lupmf' x . argsToVecs
    rng = rng' . argsToVecs

argsToVecs :: TE.ExprList [TE.EArray1 TE.EInt, TE.EReal, TE.EReal] -> TE.ExprList [TE.EArray1 TE.EInt, TE.ECVec, TE.ECVec]
argsToVecs (t :> a :> b :> TNil) = t :> realToSameSizeVec t a :> realToSameSizeVec t b :> TNil

intsToVec :: TE.UExpr (TE.EArray1 TE.EInt) -> TE.UExpr TE.ECVec
intsToVec x = TE.functionE TE.to_vector (x :> TNil)

categoricalDist :: forall t t'.TE.CategoricalTypes t t' => SimpleDist t '[t']
categoricalDist = StanDist Discrete sample lpmf lupmf rng
  where
    sample y = TE.sample y TE.categorical
    lpmf = TE.densityE TE.categorical_lpmf
    lupmf = TE.densityE TE.categorical_lupmf
    rng = case TE.genSType @t of
      TE.SInt -> TE.functionE TE.categorical_rng
      _ -> error "categorical_rng is not vectorized. For a vector of results, call from a loop."


categoricalLogitDist :: forall t . (TE.TypeOneOf t [TE.EInt, TE.EIntArray], TE.GenSType t) => SimpleDist t '[TE.ECVec]
categoricalLogitDist = StanDist Discrete sample lpmf lupmf rng
  where
    sample y = TE.sample y TE.categorical_logit
    lpmf = TE.densityE TE.categorical_logit_lpmf
    lupmf = TE.densityE TE.categorical_logit_lupmf
    rng = case TE.genSType @t of
      TE.SInt -> TE.functionE TE.categorical_logit_rng
      _ -> error "categorical_logit_rng is not vectorized. For a vector of results, call from a loop."


multinomialDist ::  (TE.TypeOneOf t [TE.ESimplex, TE.ECVec, TE.ERVec], TE.GenSType t) => StanDist TE.EIntArray '[t] [t, TE.EInt]
multinomialDist = StanDist Discrete sample lpmf lupmf rng
  where
    sample y = TE.sample y TE.multinomial
    lpmf  = TE.densityE TE.multinomial_lpmf
    lupmf  = TE.densityE TE.multinomial_lupmf
    rng  = TE.functionE TE.multinomial_rng


multinomialLogitDist :: StanDist TE.EIntArray '[TE.ECVec] '[TE.ECVec, TE.EInt]
multinomialLogitDist = StanDist Discrete sample lpmf lupmf rng
  where
    sample y = TE.sample y TE.multinomial_logit
    lpmf  = TE.densityE TE.multinomial_logit_lpmf
    lupmf  = TE.densityE TE.multinomial_logit_lupmf
    rng  = TE.functionE TE.multinomial_logit_rng

{-
normallyApproximatedBinomial :: StanDist (TE.EArray1 TE.EInt) '[TE.EArray1 TE.EInt, TE.EReal]
normallyApproximatedBinomial = StanDist Continuous sample lpdf lupdf rng
  where
    mu p t = p `TE.timesE` intsToVec t
--    sigma :: TE.UExpr TE.EReal -> TE.UExpr (TE.EArray1 TE.EInt) -> TE.UExpr TE.ECVec
    sigma p t = TE.functionE (TE.sqrt TE.SReal) (p `TE.timesE` (TE.realE 1 `TE.minusE` p) :> TNil) `TE.timesE` intsToVec t
    sample :: TE.UExpr (TE.EArray1 TE.EInt) -> TE.ExprList [TE.EArray1 TE.EInt, TE.EReal] -> TE.UStmt
    sample s (t :> p :> TNil) = TE.sample (intsToVec s) (TE.normalDensity TE.SCVec) (mu p t :> sigma p t :> TNil)
    lpdf :: TE.UExpr (TE.EArray1 TE.EInt) -> TE.ExprList [TE.EArray1 TE.EInt, TE.EReal] -> TE.UExpr TE.EReal
    lpdf s (t :> p :> TNil)  = TE.densityE (TE.normalLPDF TE.SCVec) (intsToVec t) (mu p t :> sigma p t :> TNil)
    lupdf :: TE.UExpr (TE.EArray1 TE.EInt) -> TE.ExprList [TE.EArray1 TE.EInt, TE.EReal] -> TE.UExpr TE.EReal
    lupdf s (t :> p :> TNil) = TE.densityE (TE.normalLUPDF TE.SCVec) (intsToVec t) (mu p t :> sigma p t :> TNil)
    rng ::  TE.ExprList [TE.EArray1 TE.EInt, TE.EReal] -> TE.UExpr TE.ECVec
    rng (t :> p :> TNil) = TE.functionE (TE.normalRNG TE.SCVec) (mu p t :> sigma p t > TNil)


normallyApproximatedBinomialLogit :: SME.StanVar -> StanDist SME.StanExpr
normallyApproximatedBinomialLogit tV = StanDist Continuous sample lpdf lupdf rng
  where
    pE lpE = invLogit lpE
    mu lpE = pE lpE `vecTimes` toVec tV
    sigma lpE = TE.functionE (TE.sqrt TE.SCVec) (one $ pE lpE `vecTimes` (SME.scalar "1" `TE.minusE` pE lpE) `vecTimes` toVec tV)
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
