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

module Stan.BuildingBlocks.Distributions.RealBinomial where

import qualified Stan.Language as SL
import qualified Stan.Language.Statement as SL
import Stan.Language (TypedList(..))
import Stan.Language.Recursion (hfmap)
import qualified Stan.Functions as SF
import Stan.Functions.Operators
import qualified Stan.Builder as SB
import qualified Stan.BuildingBlocks.Distributions as SBD
import qualified Stan.BuildingBlocks.ArrayHelpers as SBBA

import Effectful (Eff)

{-
import Data.Type.Equality (type (~))

import qualified Stan.ModelBuilder.TypedExpressions.Types as TE
import Stan.ModelBuilder.TypedExpressions.TypedList (TypedList(..))
import qualified Stan.ModelBuilder.TypedExpressions.Statements as TE
import qualified Stan.ModelBuilder.TypedExpressions.Indexing as TE
import qualified Stan.ModelBuilder.TypedExpressions.Operations as TE
import qualified Stan.ModelBuilder.TypedExpressions.StanFunctions as TE
import qualified Stan.ModelBuilder.Distributions as SD
import qualified Stan.ModelBuilder as SB
-}

realBinomialLogitDistM :: forall t es . (SB.StanFunctionsC es, RealBinomialT t) => Eff es (SBD.SimpleDist t '[t, t])
realBinomialLogitDistM = do
  sampleD <- realBinomialLogit @t
  lpdfD <- realBinomialLogitLPDF @t
  rngF <- realBinomialLogitRng @t
  let sample gE args = SL.sample gE sampleD args
      lpdf = SL.densityE lpdfD
      lupdf = SL.densityE lpdfD
      rng = SL.functionE rngF
  pure $ SBD.StanDist SBD.Continuous sample lpdf lupdf rng

realBinomialLogitDistSM :: forall t es . SB.StanFunctionsC es => Eff es (SBD.SimpleDist SL.EReal '[SL.EReal, SL.EReal])
realBinomialLogitDistSM = do
  sampleD <- realBinomialLogitS
  lpdfD <- realBinomialLogitLPDF_S
--  lupmfD <- realBinomialLogitLUPMF_S
  rngF <- realBinomialLogitRngS_URS
  let sample gE args = SL.sample gE sampleD args
      lpdf = SL.densityE lpdfD
      lupdf = SL.densityE lpdfD
      rng = SL.functionE rngF
  pure $ SBD.StanDist SBD.Continuous sample lpdf lupdf rng

type RealBinomialT t = (SF.VectorizedReal t
                       , SL.TypeOneOf t [SL.ECVec, SL.ERVec, SL.EMat, SL.ESqMat, SL.ERealArray]
                       , SL.TypeOneOf t [SL.ECVec, SL.ERVec]
                       , SL.BinaryResultT (SL.BElementWise SL.BMultiply) t t ~ t
                       , SL.BinaryResultT (SL.BElementWise SL.BSubtract) t t ~ t
                       , SL.BinaryResultT (SL.BElementWise SL.BAdd) t t ~ t
                       , SL.BinaryResultT SL.BSubtract SL.EInt t ~ t
                       )


realBinomialLogit :: forall t es . (SB.StanFunctionsC es, RealBinomialT t) => Eff es (SL.Density t [t, t])
realBinomialLogit = do
  _ <- realBinomialLogitLPDF @t
  pure $ SL.simpleDensity "real_binomial_logit"

realBinomialLogitLPDF :: forall t es . (RealBinomialT t, SB.StanFunctionsC es)
                      => Eff es (SL.Density t [t, t])
realBinomialLogitLPDF = do
  let f :: SL.Density t [t,t]
      f = SL.simpleDensity "real_binomial_logit_lpdf"
  SB.addDensityOnce f (SL.DataArg "succ" :> SL.DataArg "trials" :> SL.Arg "lp" :> TNil)
    $ \(s :> t :> lp :> TNil) -> SL.cwStmt $ do
    case SL.genSType @t of
      SL.SCVec -> do
        p <- SL.declareRHSNW (SL.NamedDeclSpec "p" $ SL.vectorSpec (SF.size lp)) $ SF.inv_logit lp
        pure $ SF.sum (SF.lChoose t s |+| (s |.*| SF.log p) |+| ((t |-| s) |.*| SF.log1m p))
      SL.SRVec -> do
        p <- SL.declareRHSNW (SL.NamedDeclSpec "p" $ SL.rowVectorSpec (SF.size lp)) $ SF.inv_logit lp
        pure $ SF.sum (SF.lChoose t s |+| (s |.*| SF.log p) |+| ((t |-| s) |.*| SF.log1m p))
      SL.SReal -> do
        p <- SL.declareRHSNW (SL.NamedDeclSpec "p" $ SL.realSpec) $ SF.inv_logit lp
        pure $ SF.lChoose t s |+| (s |*| SF.log p) |+| ((t |-| s) |*| SF.log1m p)
      _ -> error "realBinomialLogitLPMF: Impossible type!"

realBinomialLogitLUPDF :: forall t es . (RealBinomialT t, SB.StanFunctionsC es)
                      => Eff es (SL.Density t [t, t])
realBinomialLogitLUPDF = do
  let f :: SL.Density t [t,t]
      f = SL.simpleDensity "real_binomial_logit_lupdf"
  SB.addDensityOnce f (SL.DataArg "succ" :> SL.DataArg "trials" :> SL.Arg "lp" :> TNil)
    $ \(s :> t :> lp :> TNil) -> SL.cwStmt $ do
    case SL.genSType @t of
      SL.SCVec -> do
        p <- SL.declareRHSNW (SL.NamedDeclSpec "p" $ SL.vectorSpec (SF.size lp)) $ SF.inv_logit lp
        pure $ SF.sum $ (s |.*| SF.log p) |+| ((t |-| s) |.*| SF.log1m p)
      SL.SRVec -> do
        p <- SL.declareRHSNW (SL.NamedDeclSpec "p" $ SL.rowVectorSpec (SF.size lp)) $ SF.inv_logit lp
        pure $ SF.sum $ (s |.*| SF.log p) |+| ((t |-| s) |.*| SF.log1m p)
      SL.SReal -> do
        p <- SL.declareRHSNW (SL.NamedDeclSpec "p" $ SL.realSpec) $ SF.inv_logit lp
        pure $ (s |*| SF.log p) |+| ((t |-| s) |*| SF.log1m p)
      _ -> error "realBinomialLogitLUPMF: Impossible type!"


-- we do this via rejection sampling, using a uniform distribution for now.
realBinomialLogitRng :: forall t es . (RealBinomialT t, SB.StanFunctionsC es)
                      => Eff es (SL.Function t [t, t])
realBinomialLogitRng = do
  scalarLogitRngSF <- realBinomialLogitRngS_URS
  let f :: SL.Function t [t,t]
      f = SL.simpleFunction "real_binomial_logit_rng"
      scalarLogitRng :: SL.RealE -> SL.RealE -> SL.RealE
      scalarLogitRng n lp = SL.functionE scalarLogitRngSF (n :> lp :> TNil)
  case SL.genSType @t of
     SL.SCVec -> SB.addFunctionOnce f (SL.DataArg "trials" :> SL.Arg "lp" :> TNil)
       $ \ (n :> lp :> TNil) -> SL.cwStmt $ do
       sz <- SL.declareRHSNW (SL.NamedDeclSpec "n" $ SL.intSpec) $ SF.size lp
       let vecSpec = SL.vectorSpec sz
       samples <- SL.declareNW (SL.NamedDeclSpec "samples" vecSpec)
       SL.addStmt
         $ SL.for "k" (SL.SpecificNumbered (SL.intE 1) sz)
         $ \k -> (samples `SL.at` k) SL.|=| scalarLogitRng (n `SL.at` k) (lp `SL.at` k)
       pure samples
     SL.SRVec -> SB.addFunctionOnce f (SL.DataArg "trials" :> SL.Arg "lp" :> TNil)
       $ \ (n :> lp :> TNil) -> SL.cwStmt $ do
       sz <- SL.declareRHSNW (SL.NamedDeclSpec "n" $ SL.intSpec) $ SF.size lp
       let rowVecSpec = SL.rowVectorSpec sz
       samples <- SL.declareNW (SL.NamedDeclSpec "samples" rowVecSpec)
       SL.addStmt
         $ SL.for "k" (SL.SpecificNumbered (SL.intE 1) sz)
         $ \k -> (samples `SL.at` k) SL.|=| scalarLogitRng (n `SL.at` k) (lp `SL.at` k)
       pure samples
     SL.SReal -> SB.addFunctionOnce f (SL.DataArg "trials" :> SL.Arg "lp" :> TNil)
       $ \ (n :> lp :> TNil) -> SL.cwStmt $ pure $ scalarLogitRng n lp
     _ -> error "realBinomialLogitLPMF: Impossible type!"

realBinomialLogitS :: forall es . SB.StanFunctionsC es => Eff es (SL.Density SL.EReal [SL.EReal, SL.EReal])
realBinomialLogitS = do
  _ <- realBinomialLogitLPDF_S
  pure $ SL.simpleDensity "real_binomial_logitS"

realBinomialLogitLPDF_S :: SB.StanFunctionsC es => Eff es (SL.Density SL.EReal [SL.EReal, SL.EReal])
realBinomialLogitLPDF_S = do
  let f :: SL.Density SL.EReal [SL.EReal, SL.EReal]
      f = SL.simpleDensity "scalar_real_binomial_logit_lpdf"
  SB.addDensityOnce f (SL.DataArg "succ" :> SL.DataArg "trials" :> SL.Arg "lp" :> TNil)
    $ \(s :> t :> lp :> TNil) -> SL.cwStmt $ realBinomialLogitLPDF_S_CW t s lp

realBinomialLogitLPDF_S_CW :: SL.RealE -> SL.RealE -> SL.RealE -> SL.CodeWriter SL.RealE
realBinomialLogitLPDF_S_CW t s lp = do
  p <- SL.declareRHSNW (SL.NamedDeclSpec "p" $ SL.realSpec) $ SF.inv_logit lp
  pure $ realBinomialLogitLPDF_S_Expr t s p

realBinomialLogitLPDF_S_Expr :: SL.RealE -> SL.RealE -> SL.RealE -> SL.RealE
realBinomialLogitLPDF_S_Expr t s p = SF.lChoose t s `SL.plusE` (s |*| SF.log p) |+| ((t |-| s) |*| SF.log1m p)


realBinomialLogitLUPDF_S :: SB.StanFunctionsC es => Eff es (SL.Density SL.EReal [SL.EReal, SL.EReal])
realBinomialLogitLUPDF_S = do
  let f :: SL.Density SL.EReal [SL.EReal,SL.EReal]
      f = SL.simpleDensity "scalar_real_binomial_logit_lupdf"
  SB.addDensityOnce f (SL.DataArg "succ" :> SL.DataArg "trials" :> SL.Arg "lp" :> TNil)
    $ \(s :> t :> lp :> TNil) -> SL.cwStmt  $ do
    p <- SL.declareRHSNW (SL.NamedDeclSpec "p" $ SL.realSpec) $ SF.inv_logit lp
    pure $ (s |*| SF.log p) |+| ((t |-| s) |*| SF.log1m p)

realBinomialLogitRngS_URS :: SB.StanFunctionsC es => Eff es (SL.Function SL.EReal [SL.EReal, SL.EReal])
realBinomialLogitRngS_URS = do
  let f :: SL.Function SL.EReal [SL.EReal,SL.EReal]
      f = SL.simpleFunction "scalar_real_binomial_logit_rng"
  SB.addFunctionOnce f (SL.DataArg "trials" :> SL.Arg "lp" :> TNil)
    $ \ (n :> lp :> TNil) -> SL.cwStmt $ do
    p <- SL.declareRHSNW (SL.NamedDeclSpec "p" $ SL.realSpec) $ SF.inv_logit lp
    k <- SL.declareRHSNW (SL.NamedDeclSpec "k" $ SL.realSpec) $ n |*| p
    maxB <- SL.declareRHSNW (SL.NamedDeclSpec "maxB" $ SL.realSpec) $ SF.exp $ realBinomialLogitLPDF_S_Expr n k p
    proposal <- SL.declareRHSNW (SL.NamedDeclSpec "proposal" $ SL.realSpec) $ SF.uniform_rng (SL.realE 0) n
    let unacceptable x = SF.uniform_rng (SL.realE 0) maxB |>=| (SF.exp $ realBinomialLogitLPDF_S_Expr n x p)
    SL.addStmt $ SL.while (unacceptable proposal) $ proposal SL.|=| SF.uniform_rng (SL.realE 0) n
    pure proposal

{-

-- is this correct? We use the beta in place of the binomial just for purposes of rng/cdf
realBinomialLogitRng :: forall t md gq . (RealBinomialT t)
                      => SB.StanBuilderM md gq (SL.Function t [t, t])
realBinomialLogitRng = do
  let f :: SL.Function t [t,t]
      f = SL.simpleFunction "real_binomial_logit_rng"
      invLogit :: SL.UExpr t -> SL.UExpr t
      invLogit x = SL.functionE SL.inv_logit (x :> TNil)
      eTimes = SL.binaryOpE (SL.SElementWise SL.SMultiply)
      toVec x = SL.functionE SL.to_vector (x :> TNil)
      toRVec x = SL.functionE SL.to_row_vector (x :> TNil)
  case SL.genSType @t of
     SL.SCVec -> SB.addFunctionOnce f (SL.DataArg "trials" :> SL.Arg "lp" :> TNil)
       $ \ (n :> lp :> TNil) -> SL.writerL $ do
       sz <- SL.declareRHSNW (SL.NamedDeclSpec "n" $ SL.intSpec []) $ SL.functionE SL.size (lp :> TNil)
       let vecSpec = SL.vectorSpec sz []
       p <- SL.declareRHSNW (SL.NamedDeclSpec "p" vecSpec) $ invLogit lp
       k <- SL.declareRHSNW (SL.NamedDeclSpec "k" vecSpec) $ n `eTimes` p
       alpha <- SL.declareRHSNW (SL.NamedDeclSpec "alpha" vecSpec)  $ k `SL.plusE` SL.realE 1
       beta <- SL.declareRHSNW (SL.NamedDeclSpec "beta" vecSpec) $ n `SL.minusE` k `SL.plusE` SL.realE 1
       pure $ n `eTimes` toVec (SL.functionE SL.beta_rng (alpha :> beta :> TNil))
     SL.SRVec -> SB.addFunctionOnce f (SL.DataArg "trials" :> SL.Arg "lp" :> TNil)
       $ \ (n :> lp :> TNil) -> SL.writerL $ do
       sz <- SL.declareRHSNW (SL.NamedDeclSpec "n" $ SL.intSpec []) $ SL.functionE SL.size (lp :> TNil)
       let rowVecSpec = SL.rowVectorSpec sz []
       p <- SL.declareRHSNW (SL.NamedDeclSpec "p" rowVecSpec) $ invLogit lp
       k <- SL.declareRHSNW (SL.NamedDeclSpec "k" rowVecSpec) $ n `eTimes` p
       alpha <- SL.declareRHSNW (SL.NamedDeclSpec "kp1" rowVecSpec) $ k `SL.plusE` SL.realE 1
       beta <- SL.declareRHSNW (SL.NamedDeclSpec "beta" rowVecSpec) $ n `SL.minusE` k `SL.plusE` SL.realE 1
       pure $ n `eTimes` toRVec (SL.functionE SL.beta_rng (alpha :> beta :> TNil))
     SL.SReal -> SB.addFunctionOnce f (SL.DataArg "trials" :> SL.Arg "lp" :> TNil)
       $ \ (n :> lp :> TNil) -> SL.writerL $ do
       p <- SL.declareRHSNW (SL.NamedDeclSpec "p" $ SL.realSpec []) $ invLogit lp
       let k = n `SL.timesE` p
           alpha = k `SL.plusE` SL.realE 1
           beta = n `SL.minusE` k `SL.plusE` SL.realE 1
       pure $ n `SL.timesE` SL.functionE SL.beta_rng (alpha :> beta :> TNil)
     _ -> error "realBinomialLogitLPMF: Impossible type!"



-- is this correct? We use the beta in place of the binomial just for purposes of rng/cdf
realBinomialLogitRngS :: SB.StanBuilderM md gq (SL.Function SL.EReal [SL.EReal, SL.EReal])
realBinomialLogitRngS = do
  let f :: SL.Function SL.EReal [SL.EReal,SL.EReal]
      f = SL.simpleFunction "scalar_real_binomial_logit_rng"
      invLogit x = SL.functionE SL.inv_logit (x :> TNil)
  SB.addFunctionOnce f (SL.DataArg "trials" :> SL.Arg "lp" :> TNil)
    $ \ (n :> lp :> TNil) -> SL.writerL $ do
    p <- SL.declareRHSNW (SL.NamedDeclSpec "p" $ SL.realSpec []) $ invLogit lp
    k <- SL.declareRHSNW (SL.NamedDeclSpec "k" $ SL.realSpec []) $ n `SL.timesE` p
    let a = k `SL.plusE` SL.realE 1
        b = n `SL.minusE` k `SL.plusE` SL.realE 1
    pure $ n `SL.timesE` SL.functionE SL.beta_rng (a :> b :> TNil)

-}
