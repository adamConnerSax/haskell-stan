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
import qualified Stan.Language.Statement as SL
import Stan.Language (TypedList(..))
import Stan.Language.Recursion (hfmap)
import qualified Stan.Functions as SF
import Stan.Functions.Operators
import qualified Stan.Builder as SB
import qualified Stan.BuildingBlocks.ArrayHelpers as SBBA
import qualified Stan.BuildingBlocks.Distributions as SBD


import qualified Data.Dependent.HashMap as DHash
import qualified Data.Vector.Unboxed as VU
import qualified Stan.Builder as SB

import Effectful (Eff)

addFixedInt :: SB.AddConstJsonC SB.ModelDataT es => Text -> Int -> Eff es SL.IntE
addFixedInt t n = SB.addFixedIntJson SB.ModelData t Nothing n

addIntData :: SB.AddJsonC r es
           => SB.RowTypeTag r
           -> SL.VarName
           -> Maybe Int
           -> Maybe Int
           -> (r -> Int)
           -> Eff es SL.IntArrayE
addIntData rtt varName mLower mUpper f = do
  let cs = maybe SL.NoModifiers (SL.Modifiers . pure . SL.lowerM . SL.intE) mLower <> maybe SL.NoModifiers (SL.Modifiers . pure . SL.upperM . SL.intE) mUpper
      ndsF lE = SL.NamedDeclSpec varName $ SL.addVMs cs $ SL.intArraySpec lE
  SB.addColumnJson rtt ndsF (SB.dataSetSizeE rtt) f

addCountData :: SB.AddJsonC r es
             => SB.RowTypeTag r
             -> SL.VarName
             -> (r -> Int)
             -> Eff es SL.IntArrayE
addCountData rtt varName f = addIntData rtt varName (Just 0) Nothing f

addRealData :: SB.AddJsonC r es
            => SB.RowTypeTag r
            -> SL.VarName
            -> Maybe Double
            -> Maybe Double
            -> (r -> Double)
            -> Eff es SL.VectorE
addRealData rtt varName mLower mUpper f = do
  let cs = maybe SL.NoModifiers (SL.Modifiers . pure . SL.lowerM. SL.realE) mLower <> maybe SL.NoModifiers (SL.Modifiers . pure . SL.upperM . SL.realE) mUpper
      ndsF lE = SL.NamedDeclSpec varName $ SL.addVMs cs $ SL.vectorSpec lE
  SB.addColumnJson rtt ndsF (SB.dataSetSizeE rtt) f

addIntArrayData :: SB.AddJsonC r es
                => SB.RowTypeTag r
                -> SL.VarName
                -> SL.IntE
                -> Maybe Int
                -> Maybe Int
                -> (r -> VU.Vector Int)
                -> Eff es (SL.UExpr (SL.EArray1 (SL.EArray1 SL.EInt)))
addIntArrayData rtt varName innerSizeE mLower mUpper f = do
  let cs = maybe SL.NoModifiers (SL.Modifiers . pure . SL.lowerM . SL.intE) mLower <> maybe SL.NoModifiers (SL.Modifiers . pure . SL.upperM . SL.intE) mUpper
      ndsF lE = SL.NamedDeclSpec varName $ SL.array1Spec lE (SL.array1Spec innerSizeE $ SL.addVMs cs SL.intSpec)
  SB.addColumnJson rtt ndsF (SB.dataSetSizeE rtt) f

add2dMatrixData :: SB.AddJsonC r es
                => SB.RowTypeTag r
                -> SB.MatrixRowFromData r
                -> Maybe Double
                -> Maybe Double
                -> Eff es SL.MatrixE
add2dMatrixData rtt mrfd@(SB.MatrixRowFromData rowName ciM rl _) mLower mUpper = do
  let cs = maybe SL.NoModifiers (SL.Modifiers . pure . SL.lowerM . SL.realE) mLower <> maybe SL.NoModifiers (SL.Modifiers . pure . SL.upperM . SL.realE) mUpper
  SB.add2dMatrixJson rtt mrfd cs -- (SB.NamedDim $ SB.dataSetName rtt)  --stanType bounds f

-- This is specifically useful for things like categorical/multinomial
addArrayOfIntArrays :: SB.AddJsonC r es
                    => SB.RowTypeTag r
                    -> SL.VarName
                    -> Maybe SL.VarName
                    -> Int
                    -> (r -> [Int])
                    -> Maybe Int
                    -> Maybe Int
                    -> Eff es (SL.ArrayE (SL.EArray1 SL.EInt), SL.IntE)
addArrayOfIntArrays rtt varName widthNameM width dataFromRowF mLower mUpper = do
  let cs = maybe [] (pure . SL.lowerM . SL.intE) mLower ++ maybe [] (pure . SL.upperM . SL.intE) mUpper
      widthName = fromMaybe ("K_" <> varName) widthNameM
      ndsF rowsE = SL.NamedDeclSpec varName $ SL.array1Spec rowsE (SL.addVMs cs $ SL.intArraySpec (SL.namedE widthName SL.SInt))
  widthE <- SB.addFixedIntJson (SB.inputDataT rtt) widthName Nothing width
  arrE <- SB.addColumnJson rtt ndsF dataFromRowF
  pure (arrE, widthE)
