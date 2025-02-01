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

module Stan.BuildingBlocks.Data
  (
    module Stan.BuildingBlocks.Data
  )
where

import Prelude hiding (sum, All)

import qualified Stan.Language as SL
import qualified Stan.Builder as SB

import qualified Data.Vector.Unboxed as VU

import Effectful (Eff)

addFixedIntModel :: forall d es . SB.StanConstJsonC SB.ModelDataT d es => Text -> Int -> Eff es SL.IntE
addFixedIntModel t = SB.addFixedIntJson @_ @d SB.ErrIfDuplicate SB.ModelData t Nothing
--  let idt :: SB.InputDataType SB.ModelDataT d = SB.ModelData


addFixedIntGQ :: forall d es . SB.StanConstJsonC SB.GQDataT d es => Text -> Int -> Eff es SL.IntE
addFixedIntGQ t = SB.addFixedIntJson @_ @d SB.ErrIfDuplicate SB.GQData t Nothing

addIntData :: forall i d r es .
              SB.StanJsonC i d es
           => SB.InputDataType i d
           -> SB.RowTypeTag r
           -> SL.VarName
           -> Maybe Int
           -> Maybe Int
           -> (r -> Int)
           -> Eff es SL.IntArrayE
addIntData idt rtt varName mLower mUpper f = do
  let cs = maybe SL.NoModifiers (SL.Modifiers . pure . SL.lowerM . SL.intE) mLower <> maybe SL.NoModifiers (SL.Modifiers . pure . SL.upperM . SL.intE) mUpper
      ndsF lE = SL.NamedDeclSpec varName $ SL.addVMs cs $ SL.intArraySpec lE
  SB.addColumnJson SB.ErrIfDuplicate idt rtt ndsF (SB.dataSetSizeE rtt) f

addCountData :: forall i d r es . SB.StanJsonC i d es
             => SB.InputDataType i d
             -> SB.RowTypeTag r
             -> SL.VarName
             -> (r -> Int)
             -> Eff es SL.IntArrayE
addCountData idt rtt varName = addIntData idt rtt varName (Just 0) Nothing

addRealData :: forall i d r es . SB.StanJsonC i d es
            => SB.InputDataType i d
            -> SB.RowTypeTag r
            -> SL.VarName
            -> Maybe Double
            -> Maybe Double
            -> (r -> Double)
            -> Eff es SL.VectorE
addRealData idt rtt varName mLower mUpper f = do
  let cs = maybe SL.NoModifiers (SL.Modifiers . pure . SL.lowerM. SL.realE) mLower <> maybe SL.NoModifiers (SL.Modifiers . pure . SL.upperM . SL.realE) mUpper
      ndsF lE = SL.NamedDeclSpec varName $ SL.addVMs cs $ SL.vectorSpec lE
  SB.addColumnJson SB.ErrIfDuplicate idt rtt ndsF (SB.dataSetSizeE rtt) f

addIntArrayData :: forall i d r es .
                   SB.StanJsonC i d es
                => SB.InputDataType i d
                -> SB.RowTypeTag r
                -> SL.VarName
                -> SL.IntE
                -> Maybe Int
                -> Maybe Int
                -> (r -> VU.Vector Int)
                -> Eff es (SL.UExpr (SL.EArray1 (SL.EArray1 SL.EInt)))
addIntArrayData idt rtt varName innerSizeE mLower mUpper f = do
  let cs = maybe SL.NoModifiers (SL.Modifiers . pure . SL.lowerM . SL.intE) mLower <> maybe SL.NoModifiers (SL.Modifiers . pure . SL.upperM . SL.intE) mUpper
      ndsF lE = SL.NamedDeclSpec varName $ SL.array1Spec lE (SL.array1Spec innerSizeE $ SL.addVMs cs SL.intSpec)
  SB.addColumnJson SB.ErrIfDuplicate idt rtt ndsF (SB.dataSetSizeE rtt) f

add2dMatrixData :: forall i d r es . (SB.StanJsonC i d es, SB.StanConstJsonC i d es)
                => SB.InputDataType i d
                -> SB.RowTypeTag r
                -> SB.MatrixRowFromData r
                -> Maybe Double
                -> Maybe Double
                -> Eff es (SL.MatrixE, SL.IntE)
add2dMatrixData idt rtt mrfd@(SB.MatrixRowFromData rowName ciM rl _) mLower mUpper = do
  let cs = maybe SL.NoModifiers (SL.Modifiers . pure . SL.lowerM . SL.realE) mLower <> maybe SL.NoModifiers (SL.Modifiers . pure . SL.upperM . SL.realE) mUpper
      colName = fromMaybe ("K_" <> rowName) ciM
  colE <- SB.addFixedIntJson SB.IgnoreIfDuplicate idt colName (Just 1) rl -- add col
  let rowE = SB.dataSetSizeE rtt
  mE <- SB.add2dMatrixJson SB.ErrIfDuplicate idt rtt mrfd cs rowE colE -- (SB.NamedDim $ SB.dataSetName rtt)  --stanType bounds f
  pure (mE, colE)

-- This is specifically useful for things like categorical/multinomial
addArrayOfIntArrays :: forall i d r es . (SB.StanJsonC i d es, SB.StanConstJsonC i d es)
                    => SB.InputDataType i d
                    -> SB.RowTypeTag r
                    -> SL.VarName
                    -> Maybe SL.VarName
                    -> Int
                    -> (r -> [Int])
                    -> Maybe Int
                    -> Maybe Int
                    -> Eff es (SL.ArrayE (SL.EArray1 SL.EInt), SL.IntE)
addArrayOfIntArrays idt rtt varName widthNameM width dataFromRowF mLower mUpper = do
  let cs = maybe SL.NoModifiers (SL.Modifiers . pure . SL.lowerM . SL.intE) mLower <> maybe SL.NoModifiers (SL.Modifiers . pure . SL.upperM . SL.intE) mUpper
      widthName = fromMaybe ("K_" <> varName) widthNameM
      ndsF rowsE = SL.NamedDeclSpec varName $ SL.array1Spec rowsE (SL.addVMs cs $ SL.intArraySpec (SL.namedE widthName SL.SInt))
  widthE <- SB.addFixedIntJson SB.IgnoreIfDuplicate idt widthName Nothing width
  arrE <- SB.addColumnJson SB.ErrIfDuplicate idt rtt ndsF widthE dataFromRowF
  pure (arrE, widthE)
