{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# OPTIONS_GHC -fno-warn-overlapping-patterns #-}

module Stan.Language.Expressions
  (
    namedE
  , intE
  , realE
  , complexE
  , stringE
  , vectorE
  , matrixE
  , arrayE
  , ExprList
  , tupleE
  , functionE
  , densityE
  , unaryOpE
  , negateE
  , transposeE
  , binaryOpE
  , plusE
  , minusE
  , timesE
  , divideE
  , boolOpE
  , multiOpE
  , condE
  , sliceE
  , at
  , slice0
  , indexE
  , indexTuple
  , fstRef
  , sndRef
  , rangeIndexE
  , namedSizeE
  , sliceInner
  , sliceInnerN
  , sliceArrayAll
  , BoolE
  , IntE
  , RealE
  , ArrayE
  , IntArrayE
  , RealArrayE
  , VectorE
  , RVectorE
  , MatrixE
  , SqMatrixE
  , mRow
  , atRow
  , mCol
  , atCol
  , mAt
  )
  where

import qualified Stan.Language.Expression as SLE
import qualified Stan.Language.Recursion as SLR
import Stan.Language.Types
    ( EArray1,
      EIndexArray,
      EType(ESqMat, ERVec, EInt, EBool, EArray, EMat, ECVec, EString,
            EComplex, EReal, ETuple),
      SType(SInt),
      TypedList,
    )
import Stan.Language.Indexing
    ( Sliced,
      N0,
      s1,
      NestedVec,
      Indexed,
      SliceInnerN,
      s0, IndexedTuple )
import Stan.Language.Operations
    ( BinaryResultT,
      BinaryOp(BAdd, BDivide, BMultiply, BSubtract),
      SBinaryOp(SBoolean, SAdd, SSubtract, SMultiply, SDivide),
      UnaryOp(UNegate, UTranspose),
      UnaryResultT,
      SUnaryOp(..),
      SBoolOp,
      BoolResultT )
import Stan.Language.Functions ( Density(..), Function(..) )
import Prelude hiding (Nat)
import qualified Data.Vec.Lazy as Vec
import qualified Data.Type.Nat as DT
import Data.Type.Nat (Nat(Z, S), SNat (SZ, SS, SS'))

namedE :: SLE.VarName -> SType t -> SLE.UExpr t
namedE name st = SLR.IFix $ SLE.UVarExpr name st $ SLE.LNamed name st

intE :: Int -> SLE.UExpr EInt
intE = SLR.IFix . SLE.UL . SLE.LInt

realE :: Double -> SLE.UExpr EReal
realE = SLR.IFix . SLE.UL . SLE.LReal

complexE :: Double -> Double -> SLE.UExpr EComplex
complexE rp ip = SLR.IFix $ SLE.UL $ SLE.LComplex rp ip

stringE :: Text -> SLE.UExpr EString
stringE = SLR.IFix . SLE.UL . SLE.LString

vectorE :: [Double] -> SLE.UExpr ECVec
vectorE = SLR.IFix . SLE.UL . SLE.LVector

matrixE :: [Vec.Vec n Double] -> SLE.UExpr EMat
matrixE = SLR.IFix . SLE.UL . SLE.LMatrix

arrayE :: NestedVec n (SLE.UExpr t) -> SLE.UExpr (EArray n t)
arrayE = SLR.IFix . SLE.UL . SLE.LArray

type ExprList = TypedList SLE.UExpr

tupleE :: TypedList SLE.UExpr ts -> SLE.UExpr (ETuple ts)
tupleE = SLR.IFix . SLE.UL . SLE.LTuple

functionE :: Function rt args -> TypedList SLE.UExpr args -> SLE.UExpr rt
functionE f al = SLR.IFix $ SLE.UFunction f $ SLE.LFunction f al

densityE :: Density gt args -> SLE.UExpr gt -> TypedList SLE.UExpr args -> SLE.UExpr EReal
densityE d ge al = SLR.IFix $ SLE.UDensity d $ SLE.LDensity d ge al

unaryOpE :: SUnaryOp op -> SLE.UExpr t -> SLE.UExpr (UnaryResultT op t)
unaryOpE op e = SLR.IFix $ SLE.UL $ SLE.LUnaryOp op e

negateE :: SLE.UExpr t -> SLE.UExpr (UnaryResultT UNegate t)
negateE = unaryOpE SNegate

transposeE :: SLE.UExpr t -> SLE.UExpr (UnaryResultT UTranspose t)
transposeE = unaryOpE STranspose

binaryOpE :: SBinaryOp op -> SLE.UExpr ta -> SLE.UExpr tb -> SLE.UExpr (BinaryResultT op ta tb)
binaryOpE op ea eb = SLR.IFix $ SLE.UL $ SLE.LBinaryOp op ea eb

plusE :: SLE.UExpr ta -> SLE.UExpr tb -> SLE.UExpr (BinaryResultT BAdd ta tb)
plusE = binaryOpE SAdd

minusE :: SLE.UExpr ta -> SLE.UExpr tb -> SLE.UExpr (BinaryResultT BSubtract ta tb)
minusE = binaryOpE SSubtract

timesE :: SLE.UExpr ta -> SLE.UExpr tb -> SLE.UExpr (BinaryResultT BMultiply ta tb)
timesE = binaryOpE SMultiply

divideE :: SLE.UExpr ta -> SLE.UExpr tb -> SLE.UExpr (BinaryResultT BDivide ta tb)
divideE = binaryOpE SDivide

boolOpE :: SBoolOp op -> SLE.UExpr ta -> SLE.UExpr tb -> SLE.UExpr (BoolResultT op ta tb)
boolOpE bop ea eb = SLR.IFix $ SLE.UL $ SLE.LBinaryOp (SBoolean bop) ea eb

multiOpE :: (t ~ BinaryResultT op t t) => SBinaryOp op -> NonEmpty (SLE.UExpr t) -> SLE.UExpr t
multiOpE op es = foldl' (binaryOpE op) (head es) (tail es)

condE :: SLE.UExpr EBool -> SLE.UExpr t -> SLE.UExpr t -> SLE.UExpr t
condE ce te fe = SLR.IFix $ SLE.UL $ SLE.LCond ce te fe

sliceE :: SNat n -> SLE.UExpr EInt -> SLE.UExpr t -> SLE.UExpr (Sliced n t)
sliceE sn ie e = SLR.IFix $ SLE.UL $ SLE.LSlice sn ie e

at :: SLE.UExpr t -> SLE.UExpr EInt -> SLE.UExpr (Sliced N0 t)
at x n = sliceE s0 n x
{-# INLINEABLE at #-}

slice0 :: SLE.UExpr EInt -> SLE.UExpr t -> SLE.UExpr (Sliced N0 t)
slice0 = sliceE s0
{-# INLINEABLE slice0 #-}

indexE :: SNat n -> SLE.UExpr EIndexArray -> SLE.UExpr t -> SLE.UExpr (Indexed n t)
indexE sn ie e = SLR.IFix $ SLE.UL $ SLE.LIndex sn ie e

indexTuple :: SNat n -> SLE.UExpr t -> SLE.UExpr (IndexedTuple n t)
indexTuple sn e = SLR.IFix $ SLE.UL $ SLE.LIndexedTuple sn e

fstRef :: SLE.UExpr t -> SLE.UExpr (IndexedTuple Z t)
fstRef e = SLR.IFix $ SLE.UL $ SLE.LIndexedTuple SZ e

sndRef :: SLE.UExpr t -> SLE.UExpr (IndexedTuple (S Z) t)
sndRef e = SLR.IFix $ SLE.UL $ SLE.LIndexedTuple (SS' SZ) e

rangeIndexE :: SNat n -> Maybe (SLE.UExpr EInt) -> Maybe (SLE.UExpr EInt) -> SLE.UExpr t -> SLE.UExpr (Indexed n t)
rangeIndexE n leM ueM = indexE n (SLR.IFix $ SLE.UL $ SLE.LIntRange leM ueM)

{-
namedIndexE :: Text -> SLE.UExpr EIndexArray
namedIndexE = SLR.IFix . SLE.UIndex
-}

namedSizeE :: Text -> SLE.UExpr EInt
namedSizeE t = namedE t SInt --SLR.IFix . SLE.UIndexSize


sliceInner :: SLE.UExpr t -> SLE.UExpr EInt -> SLE.UExpr (SliceInnerN (S Z) t)
sliceInner e i = sliceE SZ i e

-- NB: We need the "go" here to add the SNat to the steps so GHC can convince itself that the lengths match up
-- This will yield a compile-time error if we try to index past the end or, same same, index something scalar.
-- That is, if n > Dimension a, this cannot be compiled.
sliceInnerN :: SLE.UExpr t -> Vec.Vec n (SLE.UExpr EInt) -> SLE.UExpr (SliceInnerN n t)
sliceInnerN e v = Vec.withDict v $ go e v where
  go :: DT.SNatI m => SLE.UExpr u -> Vec.Vec m (SLE.UExpr EInt) -> SLE.UExpr (SliceInnerN m u)
  go = go' DT.snat
  go' :: DT.SNat k -> SLE.UExpr a -> Vec.Vec k (SLE.UExpr EInt) -> SLE.UExpr (SliceInnerN k a)
  go' SZ e' _ = e'
  go' SS e' (i Vec.::: v') = go' DT.snat (sliceInner e' i) v'

-- we need this special case but that seems bad
sliceArrayAll :: forall n t . SLE.UExpr (EArray (S n) t) -> Vec.Vec (S n) (SLE.UExpr EInt) -> SLE.UExpr t
sliceArrayAll e (v Vec.::: Vec.VNil) = sliceE SZ v e
sliceArrayAll e (v Vec.::: v' Vec.::: vs) = sliceArrayAll (sliceE SZ v e) (v' Vec.::: vs)

{-
sliceEntireArray :: SLE.UExpr (EArray n t) -> Vec n (SLE.UExpr EInt) -> SLE.UExpr t
sliceEntireArray e v = Vec.withDict v $ go e v where
  go :: DT.SNatI m => SLE.UExpr u -> Vec m (SLE.UExpr EInt) -> SLE.UExpr (SliceInnerN m u)
  go = go' DT.snat
  go' :: DT.SNat k -> SLE.UExpr a -> Vec k (SLE.UExpr EInt) -> SLE.UExpr (SliceInnerN k a)
  go' SZ e' _ = e'
  go' SS e' (i ::: v') = go' DT.snat (sliceInner e' i) v'
-}

-- some type aliases for ergonomics
type BoolE = SLE.UExpr EBool
type IntE = SLE.UExpr EInt
type RealE = SLE.UExpr EReal
type ArrayE :: EType -> Type
type ArrayE t = SLE.UExpr (EArray1 t)
type IntArrayE = ArrayE EInt
type RealArrayE = ArrayE EReal
type VectorE = SLE.UExpr ECVec
type RVectorE = SLE.UExpr ERVec
type MatrixE = SLE.UExpr EMat
type SqMatrixE = SLE.UExpr ESqMat

mRow :: IntE -> MatrixE -> RVectorE
mRow = flip at
{-# INLINEABLE mRow #-}

atRow :: MatrixE -> IntE -> RVectorE
atRow = at
{-# INLINEABLE atRow #-}

mCol :: IntE -> MatrixE -> VectorE
mCol = sliceE s1
{-# INLINEABLE mCol #-}

atCol :: MatrixE -> IntE -> VectorE
atCol = flip mCol
{-# INLINEABLE atCol #-}

mAt :: MatrixE -> IntE -> IntE -> RealE
mAt m r c = mRow r m `at` c
{-# INLINEABLE mAt #-}
