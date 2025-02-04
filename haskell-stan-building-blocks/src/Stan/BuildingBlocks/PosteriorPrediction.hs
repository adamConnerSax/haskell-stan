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

module Stan.BuildingBlocks.PosteriorPrediction
  (
    module Stan.BuildingBlocks.PosteriorPrediction
  )
where

import Prelude hiding (sum, All)

import qualified Stan.Language as SL
import Stan.Functions.Operators
import qualified Stan.Builder as SB
import qualified Stan.BuildingBlocks.Distributions as SBD

import Effectful (Eff)

generatePosteriorPrediction :: SB.StanCodeC es
                            => SB.RowTypeTag r
                            -> SL.NamedDeclSpec (SL.EArray1 t)
                            -> SBD.StanDist t pts rts
                            -> SL.CodeWriter (SL.IntE -> SL.ExprList rts)
                            -> Eff es (SL.ArrayE t)
generatePosteriorPrediction rtt nds sDist psFCW = generatePosteriorPrediction' rtt nds rngE psFCW (const id)
  where rngE f n = SBD.familyRNG sDist (f n)

generatePosteriorPrediction' :: SB.StanCodeC es
                             => SB.RowTypeTag r
                             -> SL.NamedDeclSpec (SL.EArray1 t)
                             -> ((SL.IntE -> SL.ExprList rts) -> SL.IntE -> SL.UExpr t) --SMD.StanDist t pts rts
                             -> SL.CodeWriter (SL.IntE -> SL.ExprList rts)
                             -> (SL.IntE -> SL.UExpr t -> SL.UExpr t)
                             -> Eff es (SL.ArrayE t)
generatePosteriorPrediction' rtt nds rngF psFCW f = SB.inBlock SL.SBPosteriorPrediction $ do
  ppE <- SB.addFromCodeWriter $ SL.declareNW nds
  SB.addScopedFromCodeWriter $ do
    psF <- psFCW
    SL.addStmt
      $ SL.for "n" (SL.SpecificNumbered (SL.intE 1) (SL.namedE (SB.dataSetSizeName rtt) SL.SInt))
      $ \nE -> SL.sliceE SL.s0 nE ppE |=| f nE (rngF psF nE)
    return ppE

generatePosteriorPredictionV' :: SB.StanCodeC es
                              => SL.NamedDeclSpec t'
                              -> SBD.StanDist t pts rts
                              -> SL.MaybeCW (SL.ExprList rts)
                              -> (SL.UExpr t -> SL.UExpr t')
                              -> Eff es (SL.UExpr t')
generatePosteriorPredictionV' nds sDist psMCW f = SB.inBlock SL.SBPosteriorPrediction $ do
  case psMCW of
    SL.NeedsCW psCW -> do
      pp <- SB.addFromCodeWriter $ SL.declareNW nds
      SB.addScopedFromCodeWriter $ do
        ps <- psCW
        SL.addStmt $ pp |=| f (SBD.familyRNG sDist ps)
        pure pp
    SL.NoCW ps -> SB.addFromCodeWriter $ SL.declareRHSNW nds $ f (SBD.familyRNG sDist ps)

generatePosteriorPredictionV :: SB.StanCodeC es
                             => SL.NamedDeclSpec t
                             -> SBD.StanDist t pts rts
                             -> SL.MaybeCW (SL.ExprList rts)
                             -> Eff es (SL.UExpr t)
generatePosteriorPredictionV nds sDist psMCW = generatePosteriorPredictionV' nds sDist psMCW id
