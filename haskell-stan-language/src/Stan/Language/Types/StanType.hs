{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Stan.Language.Types.StanType
  (
    module Stan.Language.Types.StanType
  )
  where

import Prelude hiding (Nat)

import qualified Stan.Language.Types.EType as SLTE
import qualified Stan.Language.Types.SType as SLTS
import qualified Stan.Language.Types.TypedList as SLTT

import Data.Type.Nat (SNat(..))
import qualified Data.Type.Nat as DT
import Stan.Language.Recursion (hfmap)

import qualified Data.Text as Text

data StanType :: SLTE.EType -> Type where
  StanInt :: StanType SLTE.EInt
  StanReal :: StanType SLTE.EReal
  StanComplex :: StanType SLTE.EComplex
  StanArray :: SNat n -> StanType et -> StanType (SLTE.EArray n et)
  StanVector :: StanType SLTE.ECVec
  StanOrdered :: StanType SLTE.ECVec
  StanPositiveOrdered :: StanType SLTE.ECVec
  StanSimplex :: StanType SLTE.ECVec -- was ESimplex
  StanUnitVector :: StanType SLTE.ECVec
  StanRowVector :: StanType SLTE.ERVec
  StanMatrix :: StanType SLTE.EMat
  StanSqMatrix :: StanType SLTE.ESqMat
  StanCorrMatrix :: StanType SLTE.ESqMat
  StanCholeskyFactorCorr :: StanType SLTE.ESqMat
  StanCovMatrix :: StanType SLTE.ESqMat
  StanCholeskyFactorCov :: StanType SLTE.ESqMat
  StanTuple :: SLTT.TypedList StanType ts -> StanType (SLTE.ETuple ts)

stanIntArray :: StanType (SLTE.EArray1 SLTE.EInt)
stanIntArray = StanArray SS StanInt

stanIndexArray :: StanType SLTE.EIndexArray
stanIndexArray = stanIntArray

stan2Tuple :: StanType e1 -> StanType e2 -> StanType (SLTE.ETuple [e1, e2])
stan2Tuple st1 st2 = StanTuple (st1 SLTT.:> st2 SLTT.:> SLTT.TNil)

stan3Tuple :: StanType e1 -> StanType e2 -> StanType e3 -> StanType (SLTE.ETuple [e1, e2, e3])
stan3Tuple st1 st2 st3 = StanTuple (st1 SLTT.:> st2 SLTT.:> st3 SLTT.:> SLTT.TNil)

stanTypeName :: StanType t -> Text
stanTypeName = \case
  StanInt -> "int"
  StanReal -> "real"
  StanComplex -> "complex"
  StanArray _ _ -> "array"
  StanVector -> "vector"
  StanOrdered -> "ordered"
  StanPositiveOrdered -> "positive_ordered"
  StanSimplex -> "simplex"
  StanUnitVector -> "unit_vector"
  StanRowVector -> "row_vector"
  StanSqMatrix -> "matrix"
  StanMatrix -> "matrix"
  StanCorrMatrix -> "corr_matrix"
  StanCholeskyFactorCorr -> "cholesky_factor_corr"
  StanCovMatrix -> "cov_matrix"
  StanCholeskyFactorCov -> "cholesky_factor_cov"
  StanTuple ts -> "tuple("
                  <> Text.intercalate ", " (reverse (SLTT.foldTypedList (\st ts' -> stanTypeName st : ts') [] ts))
                  <> ")"

eTypeFromStanType :: StanType t -> SLTE.EType
eTypeFromStanType = \case
  StanInt -> SLTE.EInt
  StanReal -> SLTE.EReal
  StanComplex -> SLTE.EComplex
  StanArray sn st -> SLTE.EArray (DT.snatToNat sn) (eTypeFromStanType st)
  StanVector -> SLTE.ECVec
  StanOrdered -> SLTE.ECVec
  StanPositiveOrdered -> SLTE.ECVec
  StanSimplex -> SLTE.ECVec --ESimplex
  StanUnitVector -> SLTE.ECVec
  StanRowVector -> SLTE.ERVec
  StanMatrix -> SLTE.EMat
  StanSqMatrix -> SLTE.ESqMat
  StanCorrMatrix -> SLTE.ESqMat
  StanCholeskyFactorCorr -> SLTE.ESqMat
  StanCovMatrix -> SLTE.ESqMat
  StanCholeskyFactorCov -> SLTE.ESqMat
  StanTuple sts -> SLTE.ETuple $ reverse $ SLTT.foldTypedList (\st ets -> eTypeFromStanType st : ets) [] sts

sTypeFromStanType :: StanType t -> SLTS.SType t
sTypeFromStanType = \case
  StanInt -> SLTS.SInt
  StanReal -> SLTS.SReal
  StanComplex -> SLTS.SComplex
  StanArray sn st -> SLTS.SArray sn (sTypeFromStanType st)
  StanVector -> SLTS.SCVec
  StanOrdered -> SLTS.SCVec
  StanPositiveOrdered -> SLTS.SCVec
  StanSimplex -> SLTS.SCVec --SSimplex
  StanUnitVector -> SLTS.SCVec
  StanRowVector -> SLTS.SRVec
  StanMatrix -> SLTS.SMat
  StanSqMatrix -> SLTS.SSqMat
  StanCorrMatrix -> SLTS.SSqMat
  StanCholeskyFactorCorr -> SLTS.SSqMat
  StanCovMatrix -> SLTS.SSqMat
  StanCholeskyFactorCov -> SLTS.SSqMat
  StanTuple ts -> SLTS.STuple $ hfmap sTypeFromStanType ts
