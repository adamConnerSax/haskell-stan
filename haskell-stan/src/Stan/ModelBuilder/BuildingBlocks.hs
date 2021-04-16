{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Stan.ModelBuilder.BuildingBlocks where

import qualified Stan.ModelBuilder as SB
import qualified Stan.ModelBuilder.Expressions as SME
import qualified Stan.ModelBuilder.Distributions as SMD

import Prelude hiding (All)
import qualified Data.Map as Map

addIntData :: (Typeable d, Typeable r0)
           => SME.StanName
           -> Maybe Int
           -> Maybe Int
           -> (r0 -> Int)
           -> SB.StanBuilderM env d r0 SME.StanVar
addIntData varName mLower mUpper f = do
  let stanType =  SB.StanArray [SB.NamedDim SB.modeledDataIndexName] SME.StanInt
      bounds = case (mLower, mUpper) of
                 (Nothing, Nothing) -> ""
                 (Just l, Nothing) -> "<lower=" <> show l <> ">"
                 (Nothing, Just u) -> "<upper=" <> show u <> ">"
                 (Just l, Just u) -> "<lower=" <> show l <> ", upper=" <> show u <> ">"
  SB.addColumnJson SB.ModeledRowTag varName Nothing stanType bounds f

addCountData :: forall r0 d env.(Typeable d, Typeable r0)
             => SME.StanName
             -> (r0 -> Int)
             -> SB.StanBuilderM env d r0 SME.StanVar
addCountData varName f = addIntData varName (Just 0) Nothing f

intercept :: forall env r d. (Typeable d, Typeable r) => Text -> SME.StanExpr -> SB.StanBuilderM env r d SB.StanExpr
intercept iName alphaPriorE = do
  SB.inBlock SB.SBParameters $ SB.stanDeclare iName SB.StanReal ""
  let alphaE = SB.name iName
      interceptE = alphaE `SME.vectorSample` alphaPriorE
  SB.inBlock SB.SBModel $ SB.addExprLine "intercept" interceptE
  return alphaE

sampleDistV :: SMD.StanDist args -> args -> SB.StanBuilderM env d r0 ()
sampleDistV sDist args =  SB.inBlock SB.SBModel $ do
--  indexMap <- SB.groupIndexByName <$> SB.askGroupEnv
--  let indexBindings = Map.mapWithKey (\k _ -> SME.indexed SB.modeledDataIndexName $ SME.name k) indexMap
--      bindingStore = SME.vectorizingBindings SB.modeledDataIndexName indexBindings
  let samplingE = SMD.familySampleF sDist SB.modeledDataIndexName args
  SB.indexBindingScope $ SB.addExprLine "sampleDistV" $ SME.vectorizedOne SB.modeledDataIndexName  samplingE
{-
  samplingCode <- SB.printExprM "mrpModelBlock" bindingStore $ return samplingE
  SB.addStanLine samplingCode
-}

generateLogLikelihood :: SMD.StanDist args -> args -> SB.StanBuilderM env d r0 ()
generateLogLikelihood sDist args =  SB.inBlock SB.SBGeneratedQuantities $ do
--  indexMap <- SB.groupIndexByName <$> SB.askGroupEnv
  let dim = SME.NamedDim SB.modeledDataIndexName
  SB.stanDeclare "log_lik" (SME.StanVector dim) ""
  SB.stanForLoopB "n" Nothing SB.modeledDataIndexName $ do
--    let indexBindings  = Map.insert SB.modeledDataIndexName (SME.name "n") $ Map.mapWithKey (\k _ -> SME.indexed SB.modeledDataIndexName $ SME.name k) indexMap -- we need to index the groups.
--        bindingStore = SME.fullyIndexedBindings indexBindings
    let lhsE = SME.withIndexes (SME.name "log_lik") [dim]
        rhsE = SMD.familyLDF sDist SB.modeledDataIndexName args
        llE = lhsE `SME.eq` rhsE
    SB.addExprLine "log likelihood (in Generated Quantitites)" llE
--    llCode <- SB.printExprM "log likelihood (in Generated Quantitites)" bindingStore $ return llE
--    SB.addStanLine llCode --"log_lik[n] = binomial_logit_lpmf(S[n] | T[n], " <> modelTerms <> ")"

generatePosteriorPrediction :: SME.StanVar -> SMD.StanDist args -> args -> SB.StanBuilderM env d r0 SME.StanVar
generatePosteriorPrediction (SME.StanVar ppName ppType) sDist args = SB.inBlock SB.SBGeneratedQuantities $ do
--  indexMap <- SB.groupIndexByName <$> SB.askGroupEnv
--  let indexBindings = Map.mapWithKey (\k _ -> SME.indexed SB.modeledDataIndexName $ SME.name k) indexMap
--      bindingStore = SME.vectorizingBindings SB.modeledDataIndexName indexBindings
  let  rngE = SMD.familyRNG sDist SB.modeledDataIndexName args
--  rngCode <- SB.printExprM "posterior prediction (in Generated Quantities)" rngE
  SB.stanDeclareRHS ppName ppType "" rngE

fixedEffectsQR :: Text -> SME.StanName -> SME.StanIndexKey -> SME.StanIndexKey -> SB.StanBuilderM env d r SME.StanVar
fixedEffectsQR thinSuffix matrix rowKey colKey = do
  let ri = "R" <> thinSuffix <> "_ast_inverse"
      q = "Q" <> thinSuffix <> "_ast"
      r = "R" <> thinSuffix <> "_ast"
      qMatrixType = SME.StanMatrix (SME.NamedDim rowKey, SME.NamedDim colKey)
  SB.inBlock SB.SBParameters $ SB.stanDeclare ("theta" <> matrix) (SME.StanVector $ SME.NamedDim colKey) ""
  SB.inBlock SB.SBTransformedData $ do
    SB.stanDeclare ("mean_" <> matrix) (SME.StanVector (SME.NamedDim colKey)) ""
    SB.stanDeclare ("centered_" <> matrix) (SME.StanMatrix (SME.NamedDim rowKey, SME.NamedDim colKey)) ""
    SB.stanForLoopB "k" Nothing colKey $ do
      SB.addStanLine $ "mean_" <> matrix <> "[k] = mean(" <> matrix <> "[,k])"
      SB.addStanLine $ "centered_" <>  matrix <> "[,k] = " <> matrix <> "[,k] - mean_" <> matrix <> "[k]"
    SB.stanDeclare q qMatrixType ""
    SB.stanDeclare r (SME.StanMatrix (SME.NamedDim colKey, SME.NamedDim colKey)) ""
    SB.stanDeclare ri (SME.StanMatrix (SME.NamedDim colKey, SME.NamedDim colKey)) ""
    SB.addStanLine $ q <> " = qr_thin_Q(centered_" <> matrix <> ") * sqrt(size(" <> matrix <> ") - 1)"
    SB.addStanLine $ r <> " = qr_thin_R(centered_" <> matrix <> ") / sqrt(size(" <> matrix <> ") - 1)"
    SB.addStanLine $ ri <> " = inverse(" <> r <> ")"
  SB.inBlock SB.SBTransformedParameters $ do
    SB.stanDeclare ("beta" <> matrix) (SME.StanVector $ SME.NamedDim colKey) ""
    SB.addStanLine $ "beta" <> matrix <> " = " <> ri <> " * theta" <> matrix
  let qMatrix = SME.StanVar q qMatrixType
  return qMatrix


diagVectorFunction :: SB.StanBuilderM env d r Text
diagVectorFunction = SB.declareStanFunction "vector indexBoth(vector[] vs, int N)" $ do
--  SB.addStanLine "int vec_size = num_elements(ii)"
  SB.addStanLine "vector[N] out_vec"
  SB.stanForLoop "i" Nothing "N" $ const $ SB.addStanLine $ "out_vec[i] = vs[i, i]"
  SB.addStanLine "return out_vec"
  return "indexBoth"
