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

module Stan.BuildingBlocks.SumToZero
  (
    module Stan.BuildingBlocks.SumToZero
  )
where

import Prelude hiding (All)
import qualified Stan.Builder as SB
import qualified Stan.Language as SL
import Stan.Language ((|=|))
import qualified Stan.Functions as SF
import Stan.Functions.Operators
import Stan.Language (TypedList((:>), TNil))

import Effectful (Eff)
--import qualified Effectful.State.Static.Local as EffS
--import qualified Effectful.Fail as EffF

qSumToZeroQRF' :: SL.Function SL.ECVec '[SL.EInt]
qSumToZeroQRF' = SL.simpleFunction "Q_sum_to_zero_QR"

qSumToZeroQRF :: SL.IntE -> SL.VectorE
qSumToZeroQRF n = SL.functionE qSumToZeroQRF' (n :> TNil)

qSumToZeroQRBody :: SL.TypedList SL.UExpr '[SL.EInt] -> (SL.UStmt, SL.VectorE)
qSumToZeroQRBody (n :> TNil) = SL.cwStmt $ do
  qr <- SL.declareW "Q_r" (SL.vectorSpec (SL.intE 2 |*| n))
  let
    xp1 x = x |+| SL.realE 1
    fBody i =
      let nmi = n |-| i
      in SL.assign (qr `SL.at` i) (SL.negateE $ SF.sqrt (nmi |/| (xp1 nmi)))
      :| [SL.assign (qr `SL.at` (i |+| n)) (SF.inv_sqrt (nmi |*| (xp1 nmi)))]
  SL.addStmt $ SL.for "i" (SL.SpecificNumbered (SL.intE 1) n) $ SL.grouped . fBody
  return qr

sumToZeroQRF' :: SL.Function SL.ECVec '[SL.ECVec, SL.ECVec]
sumToZeroQRF' = SL.simpleFunction "sum_to_zero_QR"

sumToZeroQRF :: SL.VectorE -> SL.VectorE -> SL.VectorE
sumToZeroQRF v1 v2 =  SL.functionE sumToZeroQRF' (v1 :> v2 :> TNil)

sumToZeroQRBody :: SL.TypedList SL.UExpr '[SL.ECVec, SL.ECVec] -> (SL.UStmt, SL.UExpr SL.ECVec)
sumToZeroQRBody (x_raw :> qr :> TNil) = SL.cwStmt $ do
  n <- SL.declareRHSW "N" SL.intSpec (SF.size x_raw |+| SL.intE 1)
  x <- SL.declareW "x" $ SL.vectorSpec n
  x_aux <- SL.declareRHSW "x_aux" SL.realSpec $ SL.realE 0
  x_sigma <- SL.declareRHSW "x_sigma" SL.realSpec (SF.inv_sqrt (SL.intE 1 |-| (SL.realE 1 |/| n)))
  let fBody i =
        let ati = SL.slice0 i
            atiPlusN = SL.slice0 (i |+| n)
        in ati x |=| (x_aux |+| ati x_raw |+| ati qr)
           :| [x_aux |=| (x_aux |+| ati x_raw |+| atiPlusN qr)]
  SL.addStmt $ SL.for "i" (SL.SpecificNumbered (SL.intE 1) (n |-| SL.intE 1)) $ SL.grouped . fBody
  SL.addStmt $ x `SL.at` n  |=| x_aux
  return $ x_sigma |*| x

sumToZeroFunctions :: SB.StanFunctionsC es => Eff es () --SB.StanBuilderM md gq ()
sumToZeroFunctions = SB.addFunctionCodeOnce "sumToZeroQR" $ SL.grouped
    [SL.function qSumToZeroQRF' (SL.Arg "N" :> TNil) qSumToZeroQRBody
    , SL.function sumToZeroQRF' (SL.Arg "x_raw" :> SL.Arg "Q_r" :> TNil) sumToZeroQRBody
    ]

sumToZeroQR :: SB.StanFunctionsC es => SL.VarName -> SL.VectorE -> Eff es SL.VectorE
sumToZeroQR vName v_stz = do
  sumToZeroFunctions
  let vecSizeE = SF.size v_stz |+| SL.intE 1
  qr_v <- SB.inBlock SL.SBTransformedData $ SB.addFromCodeWriter $
          SL.declareRHSW ("Q_r_" <> vName) (SL.vectorSpec (SL.intE 2 |*| vecSizeE)) $ qSumToZeroQRF vecSizeE
  SB.inBlock SL.SBTransformedParameters $ SB.addFromCodeWriter
    $ SL.declareRHSW vName (SL.vectorSpec vecSizeE) $ sumToZeroQRF v_stz qr_v

softSumToZero :: SB.StanFunctionsC es => SL.VectorE -> SL.DensityWithArgs SL.EReal -> Eff es ()
softSumToZero v dw = SB.addStmtToBlock SL.SBModel $ SF.sum v SL.|~| dw

-- up to user to insure IndexArray and vector have same size
weightedSoftSumToZero :: SB.StanFunctionsC es
                      => SL.VarName -> SL.VectorE -> SL.IntArrayE -> SL.DensityWithArgs SL.EReal -> Eff es ()
weightedSoftSumToZero vName v wgtIndex prior = do
  let vecSize = SF.size wgtIndex--SL.indexSize wgtIndex
  let vecSpec = SL.vectorSpec vecSize
--  v <- SB.inBlock SB.SBParameters $ SB.stanDeclare varName vecSpec
  weights <- SB.inBlock SL.SBTransformedData $ SB.addFromCodeWriter $ do
    w <- SL.declareRHSW (vName <> "_wgts") vecSpec $ SF.rep_vector (SL.realE 0) vecSize
    let fb n = SL.slice0 n (SL.indexE SL.s0 wgtIndex w) SL.+= SL.intE 1 :| []
    SL.addStmt $ SL.for "n" (SL.SpecificNumbered (SL.intE 1) vecSize) $ SL.grouped . fb
    SL.addStmt $ w SL./= vecSize
    pure w
  SB.addStmtToBlock SL.SBModel $ SF.dot_product v weights SL.|~| prior
  pure ()

data SumToZero = STZNone
               | STZSoft (SL.DensityWithArgs SL.EReal)
               | STZSoftWeighted SL.IntArrayE (SL.DensityWithArgs SL.EReal)
               | STZQR

{-
sumToZero :: TE.UExpr TE.ECVec -> SumToZero -> SB.StanBuilderM md gq (Maybe (TE.UExpr TE.ECVec))
sumToZero _ STZNone = pure Nothing
sumToZero v (STZSoft p) = Nothing <$ softSumToZero v p
sumToZero v (STZSoftWeighted vName gi p) = Nothing <$ weightedSoftSumToZero vName v gi p
sumToZero v (STZQR vName) = Just <$> sumToZeroQR vName v
-}
