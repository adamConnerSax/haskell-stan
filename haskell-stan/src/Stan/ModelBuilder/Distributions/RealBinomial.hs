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

module Stan.ModelBuilder.Distributions.RealBinomial where

import Data.Type.Equality (type (~))

import qualified Stan.ModelBuilder.TypedExpressions.Types as TE
import Stan.ModelBuilder.TypedExpressions.TypedList (TypedList(..))
import qualified Stan.ModelBuilder.TypedExpressions.Statements as TE
import qualified Stan.ModelBuilder.TypedExpressions.Indexing as TE
import qualified Stan.ModelBuilder.TypedExpressions.Operations as TE
import qualified Stan.ModelBuilder.TypedExpressions.StanFunctions as TE
import qualified Stan.ModelBuilder.Distributions as SD
import qualified Stan.ModelBuilder as SB


realBinomialLogitDistM :: forall t md gq . RealBinomialT t => SB.StanBuilderM md gq (SD.SimpleDist t '[t, t])
realBinomialLogitDistM = do
  sampleD <- realBinomialLogit @t
  lpdfD <- realBinomialLogitLPDF @t
--  lupmfD <- realBinomialLogitLUPMF @t
  rngF <- realBinomialLogitRng @t
  let sample gE args = TE.sample gE sampleD args
      lpdf = TE.densityE lpdfD
      lupdf = TE.densityE lpdfD
      rng = TE.functionE rngF
  pure $ SD.StanDist SD.Continuous sample lpdf lupdf rng

realBinomialLogitDistSM :: forall t md gq . SB.StanBuilderM md gq (SD.SimpleDist TE.EReal '[TE.EReal, TE.EReal])
realBinomialLogitDistSM = do
  sampleD <- realBinomialLogitS
  lpdfD <- realBinomialLogitLPDF_S
--  lupmfD <- realBinomialLogitLUPMF_S
  rngF <- realBinomialLogitRngS_URS
  let sample gE args = TE.sample gE sampleD args
      lpdf = TE.densityE lpdfD
      lupdf = TE.densityE lpdfD
      rng = TE.functionE rngF
  pure $ SD.StanDist SD.Continuous sample lpdf lupdf rng

type RealBinomialT t = (TE.VectorizedReal t
                       , TE.TypeOneOf t [TE.ECVec, TE.ERVec, TE.EMat, TE.ESqMat, TE.ERealArray]
                       , TE.TypeOneOf t [TE.ECVec, TE.ERVec]
                       , TE.BinaryResultT (TE.BElementWise TE.BMultiply) t t ~ t
                       , TE.BinaryResultT (TE.BElementWise TE.BSubtract) t t ~ t
                       , TE.BinaryResultT (TE.BElementWise TE.BAdd) t t ~ t
                       , TE.BinaryResultT TE.BSubtract TE.EInt t ~ t
                       )


realBinomialLogit :: forall t md gq . RealBinomialT t => SB.StanBuilderM md gq (TE.Density t [t, t])
realBinomialLogit = do
  _ <- realBinomialLogitLPDF @t
  pure $ TE.simpleDensity "real_binomial_logit"

realBinomialLogitLPDF :: forall t md gq . (RealBinomialT t)
                      => SB.StanBuilderM md gq (TE.Density t [t, t])
realBinomialLogitLPDF = do
  let f :: TE.Density t [t,t]
      f = TE.simpleDensity "real_binomial_logit_lpdf"
      eTimes :: TE.UExpr t -> TE.UExpr t -> TE.UExpr t
      eTimes = TE.binaryOpE (TE.SElementWise TE.SMultiply)
--      eMinus = TE.binaryOpE (TE.SElementWise TE.SSubtract)
      invLogit :: TE.UExpr t -> TE.UExpr t
      invLogit x = TE.functionE TE.inv_logit (x :> TNil)
      log :: TE.UExpr t -> TE.UExpr t
      log x = TE.functionE TE.log (x :> TNil)
      log1m :: TE.UExpr t -> TE.UExpr t
      log1m x = TE.functionE TE.log1m (x :> TNil)
  SB.addDensityOnce f (TE.DataArg "succ" :> TE.DataArg "trials" :> TE.Arg "lp" :> TNil)
    $ \(s :> t :> lp :> TNil) -> TE.writerL $ do
    case TE.genSType @t of
      TE.SCVec -> do
        p <- TE.declareRHSNW (TE.NamedDeclSpec "p" $ TE.vectorSpec (TE.functionE TE.size (lp :> TNil)) []) $ invLogit lp
        let c = TE.functionE TE.lChoose (t :> s :> TNil)
            t1 = s `eTimes` log p
            t2 = (t `TE.minusE` s) `eTimes` log1m p
        pure $ TE.functionE TE.sum (c `TE.plusE` t1 `TE.plusE` t2 :> TNil)
      TE.SRVec -> do
        p <- TE.declareRHSNW (TE.NamedDeclSpec "p" $ TE.rowVectorSpec (TE.functionE TE.size (lp :> TNil)) []) $ invLogit lp
        let c = TE.functionE TE.lChoose (t :> s :> TNil)
            t1 = s `eTimes` log p
            t2 = (t `TE.minusE` s) `eTimes` log1m p
        pure $ TE.functionE TE.sum (c `TE.plusE` t1 `TE.plusE` t2 :> TNil)
      TE.SReal -> do
        p <- TE.declareRHSNW (TE.NamedDeclSpec "p" $ TE.realSpec []) $ invLogit lp
        let c :: TE.UExpr t = TE.functionE TE.lChoose (t :> s :> TNil)
            t1 = s `TE.timesE` log p
            t2 = (t `TE.minusE` s) `TE.timesE` log1m p
        pure $ c `TE.plusE` t1 `TE.plusE` t2
      _ -> error "realBinomialLogitLPMF: Impossible type!"

realBinomialLogitLUPDF :: forall t md gq . (RealBinomialT t)
                      => SB.StanBuilderM md gq (TE.Density t [t, t])
realBinomialLogitLUPDF = do
  let f :: TE.Density t [t,t]
      f = TE.simpleDensity "real_binomial_logit_lupdf"
      eTimes :: TE.UExpr t -> TE.UExpr t -> TE.UExpr t
      eTimes = TE.binaryOpE (TE.SElementWise TE.SMultiply)
      invLogit :: TE.UExpr t -> TE.UExpr t
      invLogit x = TE.functionE TE.inv_logit (x :> TNil)
      log :: TE.UExpr t -> TE.UExpr t
      log x = TE.functionE TE.log (x :> TNil)
      log1m :: TE.UExpr t -> TE.UExpr t
      log1m x = TE.functionE TE.log1m (x :> TNil)
  SB.addDensityOnce f (TE.DataArg "succ" :> TE.DataArg "trials" :> TE.Arg "lp" :> TNil)
    $ \(s :> t :> lp :> TNil) -> TE.writerL $ do
    case TE.genSType @t of
      TE.SCVec -> do
        p <- TE.declareRHSNW (TE.NamedDeclSpec "p" $ TE.vectorSpec (TE.functionE TE.size (lp :> TNil)) []) $ invLogit lp
        let t1 = s `eTimes` log p
            t2 = (t `TE.minusE` s) `eTimes` log1m p
        pure $ TE.functionE TE.sum (t1 `TE.plusE` t2 :> TNil)
      TE.SRVec -> do
        p <- TE.declareRHSNW (TE.NamedDeclSpec "p" $ TE.rowVectorSpec (TE.functionE TE.size (lp :> TNil)) []) $ invLogit lp
        let t1 = s `eTimes` log p
            t2 = (t `TE.minusE` s) `eTimes` log1m p
        pure $ TE.functionE TE.sum (t1 `TE.plusE` t2 :> TNil)
      TE.SReal -> do
        p <- TE.declareRHSNW (TE.NamedDeclSpec "p" $ TE.realSpec []) $ invLogit lp
        let t1 = s `TE.timesE` log p
            t2 = (t `TE.minusE` s) `TE.timesE` log1m p
        pure $ t1 `TE.plusE` t2
      _ -> error "realBinomialLogitLUPMF: Impossible type!"


-- we do this via rejection sampling, using a uniform distribution for now.
realBinomialLogitRng :: forall t md gq . (RealBinomialT t)
                      => SB.StanBuilderM md gq (TE.Function t [t, t])
realBinomialLogitRng = do
  scalarLogitRngSF <- realBinomialLogitRngS_URS
  let f :: TE.Function t [t,t]
      f = TE.simpleFunction "real_binomial_logit_rng"
      scalarLogitRng :: TE.RealE -> TE.RealE -> TE.RealE
      scalarLogitRng n lp = TE.functionE scalarLogitRngSF (n :> lp :> TNil)
  case TE.genSType @t of
     TE.SCVec -> SB.addFunctionOnce f (TE.DataArg "trials" :> TE.Arg "lp" :> TNil)
       $ \ (n :> lp :> TNil) -> TE.writerL $ do
       sz <- TE.declareRHSNW (TE.NamedDeclSpec "n" $ TE.intSpec []) $ TE.functionE TE.size (lp :> TNil)
       let vecSpec = TE.vectorSpec sz []
       samples <- TE.declareNW (TE.NamedDeclSpec "samples" vecSpec)
       TE.addStmt
         $ TE.for "k" (TE.SpecificNumbered (TE.intE 1) sz)
         $ \k ->
             [(samples `TE.at` k) `TE.assign` scalarLogitRng (n `TE.at` k) (lp `TE.at` k)]
       pure samples
     TE.SRVec -> SB.addFunctionOnce f (TE.DataArg "trials" :> TE.Arg "lp" :> TNil)
       $ \ (n :> lp :> TNil) -> TE.writerL $ do
       sz <- TE.declareRHSNW (TE.NamedDeclSpec "n" $ TE.intSpec []) $ TE.functionE TE.size (lp :> TNil)
       let rowVecSpec = TE.rowVectorSpec sz []
       samples <- TE.declareNW (TE.NamedDeclSpec "samples" rowVecSpec)
       TE.addStmt
         $ TE.for "k" (TE.SpecificNumbered (TE.intE 1) sz)
         $ \k ->
             [(samples `TE.at` k) `TE.assign` scalarLogitRng (n `TE.at` k) (lp `TE.at` k)]
       pure samples
     TE.SReal -> SB.addFunctionOnce f (TE.DataArg "trials" :> TE.Arg "lp" :> TNil)
       $ \ (n :> lp :> TNil) -> TE.writerL $ pure $ scalarLogitRng n lp
     _ -> error "realBinomialLogitLPMF: Impossible type!"


realBinomialLogitS :: forall md gq . SB.StanBuilderM md gq (TE.Density TE.EReal [TE.EReal, TE.EReal])
realBinomialLogitS = do
  _ <- realBinomialLogitLPDF_S
  pure $ TE.simpleDensity "real_binomial_logitS"

realBinomialLogitLPDF_S :: SB.StanBuilderM md gq (TE.Density TE.EReal [TE.EReal, TE.EReal])
realBinomialLogitLPDF_S = do
  let f :: TE.Density TE.EReal [TE.EReal, TE.EReal]
      f = TE.simpleDensity "scalar_real_binomial_logit_lpdf"
  SB.addDensityOnce f (TE.DataArg "succ" :> TE.DataArg "trials" :> TE.Arg "lp" :> TNil)
    $ \(s :> t :> lp :> TNil) -> TE.writerL $ realBinomialLogitLPDF_S_CW t s lp

realBinomialLogitLPDF_S_CW :: TE.RealE -> TE.RealE -> TE.RealE -> TE.CodeWriter TE.RealE
realBinomialLogitLPDF_S_CW t s lp = do
  let invLogit x = TE.functionE TE.inv_logit (x :> TNil)
  p <- TE.declareRHSNW (TE.NamedDeclSpec "p" $ TE.realSpec []) $ invLogit lp
  pure $ realBinomialLogitLPDF_S_Expr t s p

realBinomialLogitLPDF_S_Expr :: TE.RealE -> TE.RealE -> TE.RealE -> TE.RealE
realBinomialLogitLPDF_S_Expr t s p =
  let log x = TE.functionE TE.log (x :> TNil)
      log1m x = TE.functionE TE.log1m (x :> TNil)
      c = TE.functionE TE.lChoose (t :> s :> TNil)
      t1 = s `TE.timesE` log p
      t2 = (t `TE.minusE` s) `TE.timesE` log1m p
  in c `TE.plusE` t1 `TE.plusE` t2


realBinomialLogitLUPDF_S :: SB.StanBuilderM md gq (TE.Density TE.EReal [TE.EReal, TE.EReal])
realBinomialLogitLUPDF_S = do
  let f :: TE.Density TE.EReal [TE.EReal,TE.EReal]
      f = TE.simpleDensity "scalar_real_binomial_logit_lupdf"
      invLogit x = TE.functionE TE.inv_logit (x :> TNil)
      log x = TE.functionE TE.log (x :> TNil)
      log1m x = TE.functionE TE.log1m (x :> TNil)
  SB.addDensityOnce f (TE.DataArg "succ" :> TE.DataArg "trials" :> TE.Arg "lp" :> TNil)
    $ \(s :> t :> lp :> TNil) -> TE.writerL $ do
    p <- TE.declareRHSNW (TE.NamedDeclSpec "p" $ TE.realSpec []) $ invLogit lp
    let t1 = s `TE.timesE` log p
        t2 = (t `TE.minusE` s) `TE.timesE` log1m p
    pure $ t1 `TE.plusE` t2

realBinomialLogitRngS_URS :: SB.StanBuilderM md gq (TE.Function TE.EReal [TE.EReal, TE.EReal])
realBinomialLogitRngS_URS = do
  let f :: TE.Function TE.EReal [TE.EReal,TE.EReal]
      f = TE.simpleFunction "scalar_real_binomial_logit_rng"
      invLogit x = TE.functionE TE.inv_logit (x :> TNil)
      binomialDensity :: TE.RealE -> TE.RealE -> TE.RealE -> TE.RealE
      binomialDensity k n p = TE.functionE TE.exp (realBinomialLogitLPDF_S_Expr k n p :> TNil) --TE.densityE lpdfD k (n :> lp :> TNil)
      uniformSample :: TE.RealE -> TE.RealE -> TE.RealE
      uniformSample lo hi = TE.functionE TE.uniform_rng (lo :> hi :> TNil)
  SB.addFunctionOnce f (TE.DataArg "trials" :> TE.Arg "lp" :> TNil)
    $ \ (n :> lp :> TNil) -> TE.writerL $ do
    p <- TE.declareRHSNW (TE.NamedDeclSpec "p" $ TE.realSpec []) $ invLogit lp
    k <- TE.declareRHSNW (TE.NamedDeclSpec "k" $ TE.realSpec []) $ n `TE.timesE` p
    maxB <- TE.declareRHSNW (TE.NamedDeclSpec "maxB" $ TE.realSpec []) $ binomialDensity n k p
    proposal <- TE.declareRHSNW (TE.NamedDeclSpec "proposal" $ TE.realSpec []) $ uniformSample (TE.realE 0) n
    let geq :: TE.RealE -> TE.RealE -> TE.BoolE
        geq = TE.boolOpE TE.SGEq
        unacceptable x = uniformSample (TE.realE 0) maxB `geq` binomialDensity n x p
    TE.addStmt $ TE.while (unacceptable proposal) [proposal `TE.assign` uniformSample (TE.realE 0) n]
    pure proposal

{-

-- is this correct? We use the beta in place of the binomial just for purposes of rng/cdf
realBinomialLogitRng :: forall t md gq . (RealBinomialT t)
                      => SB.StanBuilderM md gq (TE.Function t [t, t])
realBinomialLogitRng = do
  let f :: TE.Function t [t,t]
      f = TE.simpleFunction "real_binomial_logit_rng"
      invLogit :: TE.UExpr t -> TE.UExpr t
      invLogit x = TE.functionE TE.inv_logit (x :> TNil)
      eTimes = TE.binaryOpE (TE.SElementWise TE.SMultiply)
      toVec x = TE.functionE TE.to_vector (x :> TNil)
      toRVec x = TE.functionE TE.to_row_vector (x :> TNil)
  case TE.genSType @t of
     TE.SCVec -> SB.addFunctionOnce f (TE.DataArg "trials" :> TE.Arg "lp" :> TNil)
       $ \ (n :> lp :> TNil) -> TE.writerL $ do
       sz <- TE.declareRHSNW (TE.NamedDeclSpec "n" $ TE.intSpec []) $ TE.functionE TE.size (lp :> TNil)
       let vecSpec = TE.vectorSpec sz []
       p <- TE.declareRHSNW (TE.NamedDeclSpec "p" vecSpec) $ invLogit lp
       k <- TE.declareRHSNW (TE.NamedDeclSpec "k" vecSpec) $ n `eTimes` p
       alpha <- TE.declareRHSNW (TE.NamedDeclSpec "alpha" vecSpec)  $ k `TE.plusE` TE.realE 1
       beta <- TE.declareRHSNW (TE.NamedDeclSpec "beta" vecSpec) $ n `TE.minusE` k `TE.plusE` TE.realE 1
       pure $ n `eTimes` toVec (TE.functionE TE.beta_rng (alpha :> beta :> TNil))
     TE.SRVec -> SB.addFunctionOnce f (TE.DataArg "trials" :> TE.Arg "lp" :> TNil)
       $ \ (n :> lp :> TNil) -> TE.writerL $ do
       sz <- TE.declareRHSNW (TE.NamedDeclSpec "n" $ TE.intSpec []) $ TE.functionE TE.size (lp :> TNil)
       let rowVecSpec = TE.rowVectorSpec sz []
       p <- TE.declareRHSNW (TE.NamedDeclSpec "p" rowVecSpec) $ invLogit lp
       k <- TE.declareRHSNW (TE.NamedDeclSpec "k" rowVecSpec) $ n `eTimes` p
       alpha <- TE.declareRHSNW (TE.NamedDeclSpec "kp1" rowVecSpec) $ k `TE.plusE` TE.realE 1
       beta <- TE.declareRHSNW (TE.NamedDeclSpec "beta" rowVecSpec) $ n `TE.minusE` k `TE.plusE` TE.realE 1
       pure $ n `eTimes` toRVec (TE.functionE TE.beta_rng (alpha :> beta :> TNil))
     TE.SReal -> SB.addFunctionOnce f (TE.DataArg "trials" :> TE.Arg "lp" :> TNil)
       $ \ (n :> lp :> TNil) -> TE.writerL $ do
       p <- TE.declareRHSNW (TE.NamedDeclSpec "p" $ TE.realSpec []) $ invLogit lp
       let k = n `TE.timesE` p
           alpha = k `TE.plusE` TE.realE 1
           beta = n `TE.minusE` k `TE.plusE` TE.realE 1
       pure $ n `TE.timesE` TE.functionE TE.beta_rng (alpha :> beta :> TNil)
     _ -> error "realBinomialLogitLPMF: Impossible type!"



-- is this correct? We use the beta in place of the binomial just for purposes of rng/cdf
realBinomialLogitRngS :: SB.StanBuilderM md gq (TE.Function TE.EReal [TE.EReal, TE.EReal])
realBinomialLogitRngS = do
  let f :: TE.Function TE.EReal [TE.EReal,TE.EReal]
      f = TE.simpleFunction "scalar_real_binomial_logit_rng"
      invLogit x = TE.functionE TE.inv_logit (x :> TNil)
  SB.addFunctionOnce f (TE.DataArg "trials" :> TE.Arg "lp" :> TNil)
    $ \ (n :> lp :> TNil) -> TE.writerL $ do
    p <- TE.declareRHSNW (TE.NamedDeclSpec "p" $ TE.realSpec []) $ invLogit lp
    k <- TE.declareRHSNW (TE.NamedDeclSpec "k" $ TE.realSpec []) $ n `TE.timesE` p
    let a = k `TE.plusE` TE.realE 1
        b = n `TE.minusE` k `TE.plusE` TE.realE 1
    pure $ n `TE.timesE` TE.functionE TE.beta_rng (a :> b :> TNil)

-}
