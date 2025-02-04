{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

module Stan.Functions.Operators
  (
    module Stan.Functions.Operators
  )
  where

import qualified Stan.Language.Expression as SLE
import qualified Stan.Language.Expressions as SLE
import qualified Stan.Language.Operations as SLO
import qualified Stan.Language.Indexing as SLO
import qualified Stan.Language.Statement as SLS
import qualified Stan.Language.Statements as SLS

--vectorizedRealFunction :: SFC.VectorizedReal t => Text -> SLE.UExpr t -> SLE.UExpr t
--vectorizedRealFunction fName t = SLE.functionE (SLF.simpleFunction fName) (t :> TNil)

infixr 1 <||>
infixr 2 <&&>
infix 3 |==|, |!=|
infix 4 |<|, |<=|, |>|, |>=|
infixl 5 |+|, |-|, |.+|, |.-|
infixl 6 |*|, |/|, |%|, |%/%|, |.*|, |./|
infixr 7 |^|, |.^|
infix 8 |=|, |+=|, |-=|, |*=|, |/=|, |~|

(|+|) :: SLE.UExpr ta -> SLE.UExpr tb -> SLE.UExpr (SLO.BinaryResultT SLO.BAdd ta tb)
(|+|) = SLE.binaryOpE SLO.SAdd

(|-|) :: SLE.UExpr ta -> SLE.UExpr tb -> SLE.UExpr (SLO.BinaryResultT SLO.BSubtract ta tb)
(|-|) = SLE.binaryOpE SLO.SSubtract

(|*|) :: SLE.UExpr ta -> SLE.UExpr tb -> SLE.UExpr (SLO.BinaryResultT SLO.BMultiply ta tb)
(|*|) = SLE.binaryOpE SLO.SMultiply

(|/|) :: SLE.UExpr ta -> SLE.UExpr tb -> SLE.UExpr (SLO.BinaryResultT SLO.BDivide ta tb)
(|/|) = SLE.binaryOpE SLO.SDivide

(|^|) :: SLE.UExpr ta -> SLE.UExpr tb -> SLE.UExpr (SLO.BinaryResultT SLO.BPow ta tb)
(|^|) = SLE.binaryOpE SLO.SPow

(|%|) :: SLE.UExpr ta -> SLE.UExpr tb -> SLE.UExpr (SLO.BinaryResultT SLO.BModulo ta tb)
(|%|) = SLE.binaryOpE SLO.SModulo

(|%/%|) :: SLE.UExpr ta -> SLE.UExpr tb -> SLE.UExpr (SLO.BinaryResultT SLO.BIntDivide ta tb)
(|%/%|) = SLE.binaryOpE SLO.SIntDivide

(|.+|) :: SLE.UExpr ta -> SLE.UExpr tb -> SLE.UExpr (SLO.BinaryResultT (SLO.BElementWise SLO.BAdd) ta tb)
(|.+|) = SLE.binaryOpE (SLO.SElementWise SLO.SAdd)

(|.-|) :: SLE.UExpr ta -> SLE.UExpr tb -> SLE.UExpr (SLO.BinaryResultT (SLO.BElementWise SLO.BSubtract) ta tb)
(|.-|) = SLE.binaryOpE (SLO.SElementWise SLO.SSubtract)

(|.*|) :: SLE.UExpr ta -> SLE.UExpr tb -> SLE.UExpr (SLO.BinaryResultT (SLO.BElementWise SLO.BMultiply) ta tb)
(|.*|) = SLE.binaryOpE  (SLO.SElementWise SLO.SMultiply)

(|./|) :: SLE.UExpr ta -> SLE.UExpr tb -> SLE.UExpr (SLO.BinaryResultT (SLO.BElementWise SLO.BDivide) ta tb)
(|./|) = SLE.binaryOpE  (SLO.SElementWise SLO.SDivide)

(|.^|) :: SLE.UExpr ta -> SLE.UExpr tb -> SLE.UExpr (SLO.BinaryResultT (SLO.BElementWise SLO.BPow) ta tb)
(|.^|) = SLE.binaryOpE (SLO.SElementWise SLO.SPow)

(|==|) :: SLE.UExpr ta -> SLE.UExpr tb -> SLE.UExpr (SLO.BoolResultT SLO.BEq ta tb)
(|==|) = SLE.boolOpE SLO.SEq

(|!=|) :: SLE.UExpr ta -> SLE.UExpr tb -> SLE.UExpr (SLO.BoolResultT SLO.BNEq ta tb)
(|!=|) = SLE.boolOpE SLO.SNEq

(|<|) :: SLE.UExpr ta -> SLE.UExpr tb -> SLE.UExpr (SLO.BoolResultT SLO.BLT ta tb)
(|<|) = SLE.boolOpE SLO.SLT

(|<=|) :: SLE.UExpr ta -> SLE.UExpr tb -> SLE.UExpr (SLO.BoolResultT SLO.BLEq ta tb)
(|<=|) = SLE.boolOpE SLO.SLEq

(|>|) :: SLE.UExpr ta -> SLE.UExpr tb -> SLE.UExpr (SLO.BoolResultT SLO.BGT ta tb)
(|>|) = SLE.boolOpE SLO.SGT

(|>=|) :: SLE.UExpr ta -> SLE.UExpr tb -> SLE.UExpr (SLO.BoolResultT SLO.BGEq ta tb)
(|>=|) = SLE.boolOpE SLO.SGEq

(<&&>), (<||>) :: SLE.BoolE -> SLE.BoolE -> SLE.BoolE
(<&&>) = SLE.boolOpE SLO.SAnd
(<||>) = SLE.boolOpE SLO.SOr

(!!) ::  SLE.UExpr t -> SLE.IntE -> SLE.UExpr (SLO.Sliced SLO.N0 t)
(!!) = SLE.at

(|=|) :: SLE.UExpr t -> SLE.UExpr t -> SLS.UStmt
(|=|) = SLS.assign

(|+=|) ::  (ta ~ SLO.BinaryResultT SLO.BAdd ta tb) => SLE.UExpr ta -> SLE.UExpr tb -> SLS.UStmt
(|+=|) = SLS.opAssign SLO.SAdd

(|-=|) ::  (ta ~ SLO.BinaryResultT SLO.BSubtract ta tb) => SLE.UExpr ta -> SLE.UExpr tb -> SLS.UStmt
(|-=|) = SLS.opAssign SLO.SSubtract

(|*=|) ::  (ta ~ SLO.BinaryResultT SLO.BMultiply ta tb) => SLE.UExpr ta -> SLE.UExpr tb -> SLS.UStmt
(|*=|) = SLS.opAssign SLO.SMultiply

(|/=|) ::  (ta ~ SLO.BinaryResultT SLO.BDivide ta tb) => SLE.UExpr ta -> SLE.UExpr tb -> SLS.UStmt
(|/=|) = SLS.opAssign SLO.SDivide

(|~|) ::  SLE.UExpr t -> SLS.DensityWithArgs t  -> SLS.UStmt
(|~|) = SLS.sampleW
