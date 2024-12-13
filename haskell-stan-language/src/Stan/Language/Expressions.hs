{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
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
    module Stan.Language.Expressions
  )
  where

import qualified Stan.Language.Recursion as SLR
import Stan.Language.Types
    ( Nat(Z, S),
      SNat(SZ, SS),
      EArray1,
      EIndexArray,
      EType(ESqMat, ERVec, EInt, EBool, EArray, EMat, ECVec, EString,
            EComplex, EReal),
      SType(SInt, SArray) )
import Stan.Language.TypedList ( eqTypedLists, TypedList )
import Stan.Language.Indexing
    ( Vec(..),
      Sliced,
      N0,
      s1,
      NestedVec,
      Indexed,
      SliceInnerN,
      eqNestedVec,
      eqSizeNestedVec,
      eqVec,
      nestedVecHead,
      s0 )
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

import Data.Type.Equality ((:~:)(Refl), TestEquality(testEquality))

type IndexKey = Text
type VarName = Text

-- Expressions
data LExprF :: (EType -> Type) -> EType -> Type where
  LNamed :: Text -> SType t -> LExprF r t
  LInt :: Int -> LExprF r EInt
  LReal :: Double -> LExprF r EReal
  LComplex :: Double -> Double -> LExprF r EComplex
  LString :: Text -> LExprF r EString
  LVector :: [Double] -> LExprF r ECVec
  LMatrix :: [Vec n Double] -> LExprF r EMat
  LArray :: NestedVec n (r t) -> LExprF r (EArray n t)
  LIntRange :: Maybe (r EInt) -> Maybe (r EInt) -> LExprF r (EArray (S Z) EInt)  -- NB: unexported since we only use for indexing
  LFunction :: Function rt args -> TypedList r args -> LExprF r rt
  LDensity :: Density st args -> r st -> TypedList r args -> LExprF r EReal -- e.g., binomial_lupmf(st | ns, p)
  LUnaryOp :: SUnaryOp op -> r t -> LExprF r (UnaryResultT op t)
  LBinaryOp :: SBinaryOp op -> r ta -> r tb -> LExprF r (BinaryResultT op ta tb)
  LCond :: r EBool -> r t -> r t -> LExprF r t
  LSlice :: SNat n -> r EInt -> r t -> LExprF r (Sliced n t)
  LIndex :: SNat n -> r (EArray (S Z) EInt) -> r t -> LExprF r (Indexed n t)
--  LLam :: (r ea -> r eb) -> r ea -> LExprF r (ea ::-> eb)
--  deriving (Typeable)
--  LRangeIndex :: SNat n -> Maybe (r EInt) -> Maybe (r EInt) -> r t -> LExprF r (Indexed n t)


type LExpr = SLR.IFix LExprF

lNamedE :: Text -> SType t -> LExpr t
lNamedE name  = SLR.IFix . LNamed name

namedLIndex :: Text -> LExpr EIndexArray
namedLIndex t = lNamedE t (SArray s1 SInt)

namedLSize :: Text -> LExpr EInt
namedLSize t = lNamedE t SInt

lIntE :: Int -> LExpr EInt
lIntE = SLR.IFix . LInt

instance SLR.HFunctor LExprF where
  hfmap nat = \case
    LNamed txt st -> LNamed txt st
    LInt n -> LInt n
    LReal x -> LReal x
    LComplex rp ip -> LComplex rp ip
    LString t -> LString t
    LVector xs -> LVector xs
    LMatrix ms -> LMatrix ms
    LArray nv -> LArray (fmap nat nv)
    LIntRange leM ueM -> LIntRange (fmap nat leM) (fmap nat ueM)
    LFunction f al -> LFunction f (SLR.hfmap nat al)
    LDensity d st al -> LDensity d (nat st) (SLR.hfmap nat al)
    LUnaryOp suo gta -> LUnaryOp suo (nat gta)
    LBinaryOp sbo gta gtb -> LBinaryOp sbo (nat gta) (nat gtb)
    LCond c ifTrue ifFalse -> LCond (nat c) (nat ifTrue) (nat ifFalse)
    LSlice sn g gt -> LSlice sn (nat g) (nat gt)
    LIndex n re e -> LIndex n (nat re) (nat e)
--    LLam f arg -> LLam (nat f) (nat arg)
--    LRangeIndex n le ue e -> LRangeIndex n (fmap nat le) (fmap nat ue) (nat e)


instance SLR.HTraversable LExprF where
  htraverse nat = \case
    LNamed txt st -> pure $ LNamed txt st
    LInt n -> pure $ LInt n
    LReal x -> pure $ LReal x
    LComplex x y -> pure $ LComplex x y
    LString t -> pure $ LString t
    LVector xs -> pure $ LVector xs
    LMatrix ms -> pure $ LMatrix ms
    LArray nv -> LArray <$> traverse nat nv
    LIntRange leM ueM -> LIntRange <$> traverse nat leM <*> traverse nat ueM
    LFunction f al -> LFunction f <$> SLR.htraverse nat al
    LDensity d st al -> LDensity d <$> nat st <*> SLR.htraverse nat al
    LUnaryOp suo ata -> LUnaryOp suo <$> nat ata
    LBinaryOp sbo ata atb -> LBinaryOp sbo <$> nat ata <*> nat atb
    LCond c ifTrue ifFalse -> LCond <$> nat c <*> nat ifTrue <*> nat ifFalse
    LSlice sn a at' -> LSlice sn <$> nat a <*> nat at'
    LIndex n re e -> LIndex n <$> nat re <*> nat e
--    LLam f arg -> LLam <$> nat f <*> nat arg
--    LRangeIndex n le ue e -> LRangeIndex n <$> traverse nat le <*> traverse nat ue <*> nat e
  hmapM = SLR.htraverse

-- UEXpr represents expressions with context lookups to resolve
data UExprF :: (EType -> Type) -> EType -> Type where
  UL :: LExprF r et -> UExprF r et
  UIndex :: IndexKey -> UExprF r EIndexArray
  UIndexSize :: IndexKey -> UExprF r EInt
  UVarExpr :: VarName -> SType t -> LExprF r t -> UExprF r t


type UExpr = SLR.IFix UExprF

instance SLR.HFunctor UExprF where
  hfmap nat = \case
    UL le -> UL $ SLR.hfmap nat le
    UIndex txt -> UIndex txt
    UIndexSize txt -> UIndexSize txt
    UVarExpr vn st e -> UVarExpr vn st $ SLR.hfmap nat e

instance SLR.HTraversable UExprF where
  htraverse nat = \case
    UL le -> UL <$> SLR.htraverse nat le
    UIndex txt -> pure $ UIndex txt
    UIndexSize txt -> pure $ UIndexSize txt
    UVarExpr vn st e -> UVarExpr vn st <$> SLR.htraverse nat e
  hmapM = SLR.htraverse


namedE :: Text -> SType t -> UExpr t
namedE name st = SLR.IFix $ UVarExpr name st $ LNamed name st

intE :: Int -> UExpr EInt
intE = SLR.IFix . UL . LInt

realE :: Double -> UExpr EReal
realE = SLR.IFix . UL . LReal

complexE :: Double -> Double -> UExpr EComplex
complexE rp ip = SLR.IFix $ UL $ LComplex rp ip

stringE :: Text -> UExpr EString
stringE = SLR.IFix . UL . LString

vectorE :: [Double] -> UExpr ECVec
vectorE = SLR.IFix . UL . LVector

matrixE :: [Vec n Double] -> UExpr EMat
matrixE = SLR.IFix . UL . LMatrix

arrayE :: NestedVec n (UExpr t) -> UExpr (EArray n t)
arrayE = SLR.IFix . UL . LArray

type ExprList = TypedList UExpr

functionE :: Function rt args -> TypedList UExpr args -> UExpr rt
functionE f al = SLR.IFix $ UL $ LFunction f al

densityE :: Density gt args -> UExpr gt -> TypedList UExpr args -> UExpr EReal
densityE d ge al = SLR.IFix $ UL $ LDensity d ge al

unaryOpE :: SUnaryOp op -> UExpr t -> UExpr (UnaryResultT op t)
unaryOpE op e = SLR.IFix $ UL $ LUnaryOp op e

negateE :: UExpr t -> UExpr (UnaryResultT UNegate t)
negateE = unaryOpE SNegate

transposeE :: UExpr t -> UExpr (UnaryResultT UTranspose t)
transposeE = unaryOpE STranspose

binaryOpE :: SBinaryOp op -> UExpr ta -> UExpr tb -> UExpr (BinaryResultT op ta tb)
binaryOpE op ea eb = SLR.IFix $ UL $ LBinaryOp op ea eb

plusE :: UExpr ta -> UExpr tb -> UExpr (BinaryResultT BAdd ta tb)
plusE = binaryOpE SAdd

minusE :: UExpr ta -> UExpr tb -> UExpr (BinaryResultT BSubtract ta tb)
minusE = binaryOpE SSubtract

timesE :: UExpr ta -> UExpr tb -> UExpr (BinaryResultT BMultiply ta tb)
timesE = binaryOpE SMultiply

divideE :: UExpr ta -> UExpr tb -> UExpr (BinaryResultT BDivide ta tb)
divideE = binaryOpE SDivide

boolOpE :: SBoolOp op -> UExpr ta -> UExpr tb -> UExpr (BoolResultT op ta tb)
boolOpE bop ea eb = SLR.IFix $ UL $ LBinaryOp (SBoolean bop) ea eb

multiOpE :: (t ~ BinaryResultT op t t) => SBinaryOp op -> NonEmpty (UExpr t) -> UExpr t
multiOpE op es = foldl' (binaryOpE op) (head es) (tail es)

condE :: UExpr EBool -> UExpr t -> UExpr t -> UExpr t
condE ce te fe = SLR.IFix $ UL $ LCond ce te fe

sliceE :: SNat n -> UExpr EInt -> UExpr t -> UExpr (Sliced n t)
sliceE sn ie e = SLR.IFix $ UL $ LSlice sn ie e

at :: UExpr t -> UExpr EInt -> UExpr (Sliced N0 t)
at x n = sliceE s0 n x
{-# INLINEABLE at #-}

slice0 :: UExpr EInt -> UExpr t -> UExpr (Sliced N0 t)
slice0 = sliceE s0
{-# INLINEABLE slice0 #-}

indexE :: SNat n -> UExpr EIndexArray -> UExpr t -> UExpr (Indexed n t)
indexE sn ie e = SLR.IFix $ UL $ LIndex sn ie e

rangeIndexE :: SNat n -> Maybe (UExpr EInt) -> Maybe (UExpr EInt) -> UExpr t -> UExpr (Indexed n t)
rangeIndexE n leM ueM = indexE n (SLR.IFix $ UL $ LIntRange leM ueM)

namedIndexE :: Text -> UExpr EIndexArray
namedIndexE = SLR.IFix . UIndex

namedSizeE :: Text -> UExpr EInt
namedSizeE = SLR.IFix . UIndexSize

sliceInner :: UExpr t -> UExpr EInt -> UExpr (SliceInnerN (S Z) t)
sliceInner e i = sliceE SZ i e

-- NB: We need the "go" here to add the SNat to the steps so GHC can convince itself that the lengths match up
-- This will yield a compile-time error if we try to index past the end or, same same, index something scalar.
-- That is, if n > Dimension a, this cannot be compiled.
sliceInnerN :: UExpr t -> Vec n (UExpr EInt) -> UExpr (SliceInnerN n t)
sliceInnerN e v = Vec.withDict v $ go e v where
  go :: DT.SNatI m => UExpr u -> Vec m (UExpr EInt) -> UExpr (SliceInnerN m u)
  go = go' DT.snat
  go' :: DT.SNat k -> UExpr a -> Vec k (UExpr EInt) -> UExpr (SliceInnerN k a)
  go' SZ e' _ = e'
  go' SS e' (i ::: v') = go' DT.snat (sliceInner e' i) v'

--zeroDArray :: UExpr (EArray Z t) -> UExpr t
--zeroDArray = unsafecoerce
-- we need this special case but that seems bad
sliceArrayAll :: forall n t . UExpr (EArray (S n) t) -> Vec (S n) (UExpr EInt) -> UExpr t
sliceArrayAll e (v Vec.::: VNil) = sliceE SZ v e
sliceArrayAll e (v Vec.::: v' Vec.::: vs) = sliceArrayAll (sliceE SZ v e) (v' Vec.::: vs)

{-
sliceEntireArray :: UExpr (EArray n t) -> Vec n (UExpr EInt) -> UExpr t
sliceEntireArray e v = Vec.withDict v $ go e v where
  go :: DT.SNatI m => UExpr u -> Vec m (UExpr EInt) -> UExpr (SliceInnerN m u)
  go = go' DT.snat
  go' :: DT.SNat k -> UExpr a -> Vec k (UExpr EInt) -> UExpr (SliceInnerN k a)
  go' SZ e' _ = e'
  go' SS e' (i ::: v') = go' DT.snat (sliceInner e' i) v'
-}

-- some type aliases for ergonomics
type BoolE = UExpr EBool
type IntE = UExpr EInt
type RealE = UExpr EReal
type ArrayE :: EType -> Type
type ArrayE t = UExpr (EArray1 t)
type IntArrayE = ArrayE EInt
type RealArrayE = ArrayE EReal
type VectorE = UExpr ECVec
type RVectorE = UExpr ERVec
type MatrixE = UExpr EMat
type SqMatrixE = UExpr ESqMat

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


lExprTypeIs :: LExpr t -> SType t' -> Bool
lExprTypeIs le st = case eqLExprType le (lNamedE "" st) of
  Just Refl -> True
  Nothing -> False

eqLExpr :: LExpr ta -> LExpr tb -> Bool
eqLExpr la lb = case eqLExprType la lb of
  Just Refl -> eqLExprOf la lb
  Nothing -> False

-- This returns some false negatives, but will certainly work on identical expressions
eqLExprType :: LExpr ta -> LExpr tb -> Maybe (ta :~: tb)
eqLExprType = go
  where
    go :: LExpr ta -> LExpr tb -> Maybe (ta :~: tb)
    go (SLR.IFix (LNamed _ sta)) (SLR.IFix (LNamed _ stb)) = testEquality sta stb
    go (SLR.IFix (LInt _)) (SLR.IFix (LInt _)) = Just Refl
    go (SLR.IFix (LReal _)) (SLR.IFix (LReal _)) = Just Refl
    go (SLR.IFix (LComplex _ _)) (SLR.IFix (LComplex _ _)) = Just Refl
    go (SLR.IFix (LString _)) (SLR.IFix (LString _)) = Just Refl
    go (SLR.IFix (LVector _)) (SLR.IFix (LVector _)) = Just Refl
    go (SLR.IFix (LMatrix _)) (SLR.IFix (LMatrix _)) = Just Refl
    go (SLR.IFix (LArray nv)) (SLR.IFix (LArray nv')) = do
      Refl <- eqSizeNestedVec nv nv'
      Refl <- go (nestedVecHead nv) (nestedVecHead nv')
      pure Refl
    go (SLR.IFix (LIntRange _ _)) (SLR.IFix (LIntRange _ _)) = Just Refl
    go (SLR.IFix (LFunction (Function _ sta _) _)) (SLR.IFix (LFunction (Function _ stb _) _)) = testEquality sta stb
    go (SLR.IFix (LFunction (IdentityFunction sta) _)) (SLR.IFix (LFunction (IdentityFunction stb) _)) = testEquality sta stb
    go (SLR.IFix (LDensity _ _ _)) (SLR.IFix (LDensity _ _ _)) = Just Refl
    go (SLR.IFix (LUnaryOp opa ea)) (SLR.IFix (LUnaryOp opb eb)) = do
      Refl <- testEquality opa opb
      Refl <- go ea eb
      pure Refl
    go (SLR.IFix (LBinaryOp opa lhsa rhsa)) (SLR.IFix (LBinaryOp opb lhsb rhsb)) = do
      Refl <- testEquality opa opb
      Refl <- go lhsa lhsb
      Refl <- go rhsa rhsb
      pure Refl
    go (SLR.IFix (LCond _ ea _)) (SLR.IFix (LCond _ eb _)) = do
      Refl <- go ea eb
      pure Refl
    go (SLR.IFix (LIndex sna _ ea)) (SLR.IFix (LIndex snb _ eb)) = do
      let eqSNatWith :: DT.SNatI n => DT.SNat m -> Maybe (n :~: m)
          eqSNatWith sm = DT.withSNat sm DT.eqNat
          eqSNat :: DT.SNat n -> DT.SNat m -> Maybe (n :~: m)
          eqSNat sn sm = DT.withSNat sn $ eqSNatWith sm
      Refl <- eqSNat sna snb
      Refl <- go ea eb
      return Refl
    go _ _ = Nothing

eqLExprOf :: LExpr ta -> LExpr ta -> Bool
eqLExprOf = go
  where
    go :: LExpr ta -> LExpr ta -> Bool
    go (SLR.IFix (LNamed na _)) (SLR.IFix (LNamed nb _)) = na == nb
    go (SLR.IFix (LInt n)) (SLR.IFix (LInt m)) = n == m
    go (SLR.IFix (LReal x)) (SLR.IFix (LReal y)) = x == y
    go (SLR.IFix (LComplex xr xi)) (SLR.IFix (LComplex yr yi)) = xr == yr && xi == yi
    go (SLR.IFix (LString sa)) (SLR.IFix (LString sb)) = sa == sb
    go (SLR.IFix (LVector xs)) (SLR.IFix (LVector ys)) = xs == ys
    go (SLR.IFix (LMatrix vs)) (SLR.IFix (LMatrix vs')) = getAll $ mconcat $ All <$> zipWith eqVec vs vs'
    go (SLR.IFix (LArray nv)) (SLR.IFix (LArray nv')) = case eqSizeNestedVec nv nv' of
      Just Refl -> eqNestedVec eqLExprOf nv nv'
      Nothing -> False
    go (SLR.IFix (LIntRange mla mua)) (SLR.IFix (LIntRange mlb mub)) =
      let cm :: Maybe (LExpr EInt) -> Maybe (LExpr EInt) -> Bool
          cm Nothing Nothing = True
          cm (Just a) (Just b) = go a b
          cm _ _ = False
      in cm mla mlb && cm mua mub
    go (SLR.IFix (LFunction (Function fna _ ata) ala)) (SLR.IFix (LFunction (Function fnb _ atb) alb)) =
      let eqArgs = case testEquality ata atb of -- given lists are same
            Just Refl -> case testEquality ata atb of -- reqwritten lists are same
              Just Refl -> eqTypedLists go ala alb -- given args are same
              Nothing -> False
            Nothing -> False
      in fna == fnb && eqArgs
    go (SLR.IFix (LFunction (IdentityFunction _) _)) (SLR.IFix (LFunction (IdentityFunction _) _)) = True
    go (SLR.IFix (LDensity (Density dna gta ata) _ ala)) (SLR.IFix (LDensity (Density dnb gtb atb) _ alb)) =
      let eqGivens = case testEquality gta gtb of
            Just Refl -> True
            Nothing -> False
          eqArgs =  case testEquality ata atb of
            Just Refl -> case testEquality ata atb of -- reqwritten lists are same
              Just Refl -> eqTypedLists go ala alb
              Nothing -> False
            Nothing -> False
      in dna == dnb && eqGivens && eqArgs
    go (SLR.IFix (LUnaryOp opa ea)) (SLR.IFix (LUnaryOp opb eb)) = case testEquality opa opb of
      Just Refl -> case eqLExprType ea eb of
        Just Refl -> go ea eb
        Nothing -> False
      Nothing -> False
    go (SLR.IFix (LBinaryOp opa lhsa rhsa)) (SLR.IFix (LBinaryOp opb lhsb rhsb)) = case testEquality opa opb of
      Just Refl -> case eqLExprType lhsa lhsb of
        Just Refl -> case eqLExprType rhsa rhsb of
          Just Refl -> go lhsa lhsb && go rhsa rhsb
          Nothing -> False
        Nothing -> False
      Nothing -> False
    go (SLR.IFix (LCond ca lhsa rhsa)) (SLR.IFix (LCond cb lhsb rhsb)) = go ca cb && go lhsa lhsb && go rhsa rhsb
    go (SLR.IFix (LIndex _ iea ea)) (SLR.IFix (LIndex _ ieb eb)) =
      go iea ieb && case eqLExprType ea eb of
                      Just Refl -> go ea eb
                      Nothing -> False
    go _ _ = False

-- This is either very cool or very dangerous
-- replace each lookup with a blank thing of same type just for typechecking purposes
uExprToSameTypeLExpr :: UExpr t -> LExpr t
uExprToSameTypeLExpr = SLR.iCata f where
  f :: UExprF LExpr SLR.~> LExpr
  f = \case
    UL le -> SLR.IFix le
    UIndex _ -> lNamedE "" (SArray s1 SInt)
    UIndexSize _ -> lNamedE "" SInt
    UVarExpr _ _ le -> SLR.IFix le

exprTypeIs :: UExpr t -> SType t' -> Bool
exprTypeIs ue = lExprTypeIs (uExprToSameTypeLExpr ue)


{-
-- we shouldn't export this constructor.
-- You should only be able to make via the function below.
data Var :: EType -> Type where
  Var :: Text -> StanType t -> UExpr t -> Var t

varName :: Var t -> Text
varName (Var n _ _) = n

varStanType :: Var t -> StanType t
varStanType (Var _ x _) = x

varSType :: Var t -> SType t
varSType = sTypeFromStanType . varStanType

varE :: Var t -> UExpr t
varE (Var _ _ ue) = ue

var :: Text -> StanType t -> Var t
var n st = Var n st $ namedE n $ sTypeFromStanType st
-}
{-
data ContainerOf v a where
  InnerSliceable :: Sliced N0 v ~ a => UExpr v -> ContainerOf v a
  Functional :: (IntE -> UExpr t) -> ContainerOf EVoid a

type RealContainer = ContainerOf EReal
type IntContainer = ContainerOf EInt
type VecContainer = ContainerOf ECVec
-}
