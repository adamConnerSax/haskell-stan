{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use for_" #-}
{-# HLINT ignore "Use camelCase" #-}
{-# LANGUAGE QuantifiedConstraints #-}

module Stan.BuildingBlocks.LogLikelihood
  (
    module Stan.BuildingBlocks.LogLikelihood
  )
where

import Prelude hiding (sum, All)

import qualified Stan.Language as SL
import qualified Stan.Builder as SB
import qualified Stan.BuildingBlocks.Distributions as SBD

import qualified Data.Dependent.HashMap as DHash

import Effectful (Eff)

generateLogLikelihood :: SB.StanCodeC es
                      => SB.RowTypeTag r
                      -> SBD.StanDist t pts rts
                      -> SL.CodeWriter (SL.IntE -> SL.ExprList pts)
                      -> SL.CodeWriter (SL.IntE -> SL.UExpr t)
                      -> Eff es ()
generateLogLikelihood rtt sDist slicedArgsFCW slicedYFCW =
  generateLogLikelihood' $ addToLLSet rtt (LLDetails (SBD.familyLDF sDist) slicedArgsFCW slicedYFCW) emptyLLSet

-- 2nd arg returns something which might need slicing at the loop index for paramters that depend on the index
-- 3rd arg also
data LLDetails r = forall t pts . LLDetails
                   (SL.UExpr t -> SL.ExprList pts -> SL.RealE) --(SMD.StanDist t pts rts)
                   (SL.CodeWriter (SL.IntE -> SL.ExprList pts))
                   (SL.CodeWriter (SL.IntE -> SL.UExpr t))
--  LLDetails :: forall args.SMD.StanDist args -> SB.StanBuilderM md gq args -> SME.StanVar -> LLDetails md gq r

newtype LLDetailsList r = LLDetailsList [LLDetails r]

addDetailsLists :: LLDetailsList r -> LLDetailsList r -> LLDetailsList r
addDetailsLists (LLDetailsList x) (LLDetailsList y) = LLDetailsList (x <> y)

type LLSet = DHash.DHashMap SB.RowTypeTag LLDetailsList

emptyLLSet :: LLSet
emptyLLSet = DHash.empty

addToLLSet :: SB.RowTypeTag r -> LLDetails r -> LLSet  -> LLSet
addToLLSet rtt d llSet = DHash.insertWith addDetailsLists rtt (LLDetailsList [d]) llSet

mergeLLSets ::  LLSet -> LLSet -> LLSet
mergeLLSets = DHash.unionWith addDetailsLists

-- we return RowTypeTag from doOne so that DHash traversal can infer types, I think.
generateLogLikelihood' :: forall es . SB.StanCodeC es => LLSet -> Eff es ()
generateLogLikelihood' llSet =  SB.inBlock SL.SBLogLikelihood $ do
  let prependSizeName rtt (LLDetailsList ds) ls = Prelude.replicate (Prelude.length ds) (SB.dataSetSizeName rtt) ++ ls
  llSizeListNE <- case nonEmpty (DHash.foldrWithKey prependSizeName [] llSet) of
    Nothing -> SB.buildError "generateLogLikelihood': empty set of log-likelihood details given"
    Just x -> return x
  let namedIntE n = SL.namedE n SL.SInt
      llSizeE = SL.multiOpE SL.SAdd $ fmap namedIntE llSizeListNE
  logLikE <- SB.addFromCodeWriter $ SL.declareNW $ SL.NamedDeclSpec "log_lik" $ SL.vectorSpec llSizeE
  let doOne :: SB.RowTypeTag a -> LLDetails a -> StateT [SL.UExpr SL.EInt] (Eff es) (SB.RowTypeTag a)
      doOne rtt (LLDetails df pFCW yFCW) = do
        prevSizes <- get
        let --sizeE =  SL.multiOpE SL.SAdd $ namedIntE "n" :| prevSizes
        lift $ SB.addScopedFromCodeWriter $ do
          pF <- pFCW
          yF <- yFCW
          SL.addStmt $ SL.for "n" (SL.SpecificNumbered (SL.intE 1) (SB.dataSetSizeE rtt))
            $ \nE -> SL.sliceE SL.s0 nE logLikE `SL.assign` df (yF nE) (pF nE)
        put $ SL.namedE (SB.dataSetSizeName rtt) SL.SInt: prevSizes
        pure rtt
      doList :: SB.RowTypeTag a -> LLDetailsList a -> StateT [SL.UExpr SL.EInt] (Eff es) (SB.RowTypeTag a)
      doList rtt (LLDetailsList lls) = traverse_ (doOne rtt) lls >> pure rtt
  _ <- evalStateT (DHash.traverseWithKey doList llSet) []
  pure ()
