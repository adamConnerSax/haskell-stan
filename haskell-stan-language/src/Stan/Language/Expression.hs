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
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# OPTIONS_GHC -fno-warn-overlapping-patterns #-}

module Stan.Language.Expression
  (
    module Stan.Language.Expression
  )
  where

import qualified Stan.Language.Recursion as SLR
import Stan.Language.Types
    ( EIndexArray,
      EType(EInt, EBool, EArray, EMat, ECVec, EString,
            EComplex, EReal, ETuple),
      SType(SInt, SArray),
      TypedList,
      eqTypedLists
    )
import Stan.Language.Indexing
    ( Vec(..),
      Sliced,
      s1,
      NestedVec,
      Indexed,
      eqNestedVec,
      eqSizeNestedVec,
      eqVec,
      nestedVecHead,
      IndexedTuple )
import Stan.Language.Operations
    ( BinaryResultT,
      SBinaryOp,
      UnaryResultT,
      SUnaryOp(..))
import Stan.Language.Functions ( Density(..), Function(..) )
import Prelude hiding (Nat)
import qualified Data.Type.Nat as DT
import Data.Type.Nat (Nat(Z, S), SNat)

import Data.Type.Equality ((:~:)(Refl), TestEquality(testEquality))

type IndexKey = Text
type VarName = Text

-- Expression
data LExprF :: (EType -> Type) -> EType -> Type where
  LNamed :: VarName -> SType t -> LExprF r t
  LInt :: Int -> LExprF r EInt
  LReal :: Double -> LExprF r EReal
  LComplex :: Double -> Double -> LExprF r EComplex
  LString :: Text -> LExprF r EString
  LVector :: [Double] -> LExprF r ECVec
  LMatrix :: [Vec n Double] -> LExprF r EMat
  LArray :: NestedVec n (r t) -> LExprF r (EArray n t)
  LIntRange :: Maybe (r EInt) -> Maybe (r EInt) -> LExprF r (EArray (S Z) EInt)  -- NB: unexported since we only use for indexing
  LTuple :: TypedList r ts -> LExprF r (ETuple ts)
  LFunction :: Function rt args -> TypedList r args -> LExprF r rt
  LDensity :: Density st args -> r st -> TypedList r args -> LExprF r EReal -- e.g., binomial_lupmf(st | ns, p)
  LUnaryOp :: SUnaryOp op -> r t -> LExprF r (UnaryResultT op t)
  LBinaryOp :: SBinaryOp op -> r ta -> r tb -> LExprF r (BinaryResultT op ta tb)
  LCond :: r EBool -> r t -> r t -> LExprF r t
  LSlice :: SNat n -> r EInt -> r t -> LExprF r (Sliced n t)
  LIndex :: SNat n -> r (EArray (S Z) EInt) -> r t -> LExprF r (Indexed n t)
  LIndexedTuple :: SNat n -> r t -> LExprF r (IndexedTuple n t)

type LExpr = SLR.IFix LExprF

lNamedE :: VarName -> SType t -> LExpr t
lNamedE name  = SLR.IFix . LNamed name

namedLIndex :: VarName -> LExpr EIndexArray
namedLIndex t = lNamedE t (SArray s1 SInt)

namedLSize :: VarName -> LExpr EInt
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
    LTuple ts -> LTuple $ SLR.hfmap nat ts
    LFunction f al -> LFunction f (SLR.hfmap nat al)
    LDensity d st al -> LDensity d (nat st) (SLR.hfmap nat al)
    LUnaryOp suo gta -> LUnaryOp suo (nat gta)
    LBinaryOp sbo gta gtb -> LBinaryOp sbo (nat gta) (nat gtb)
    LCond c ifTrue ifFalse -> LCond (nat c) (nat ifTrue) (nat ifFalse)
    LSlice sn g gt -> LSlice sn (nat g) (nat gt)
    LIndex n re e -> LIndex n (nat re) (nat e)
    LIndexedTuple n e -> LIndexedTuple n (nat e)
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
    LTuple ts -> LTuple <$> SLR.htraverse nat ts
    LFunction f al -> LFunction f <$> SLR.htraverse nat al
    LDensity d st al -> LDensity d <$> nat st <*> SLR.htraverse nat al
    LUnaryOp suo ata -> LUnaryOp suo <$> nat ata
    LBinaryOp sbo ata atb -> LBinaryOp sbo <$> nat ata <*> nat atb
    LCond c ifTrue ifFalse -> LCond <$> nat c <*> nat ifTrue <*> nat ifFalse
    LSlice sn a at' -> LSlice sn <$> nat a <*> nat at'
    LIndex n re e -> LIndex n <$> nat re <*> nat e
    LIndexedTuple n e -> LIndexedTuple n <$> nat e
--    LLam f arg -> LLam <$> nat f <*> nat arg
--    LRangeIndex n le ue e -> LRangeIndex n <$> traverse nat le <*> traverse nat ue <*> nat e
  hmapM = SLR.htraverse

-- UEXpr represents expressions with context lookups to resolve
data UExprF :: (EType -> Type) -> EType -> Type where
  UL :: LExprF r et -> UExprF r et
  UIndex :: IndexKey -> UExprF r EIndexArray
  UIndexSize :: IndexKey -> UExprF r EInt
  UVarExpr :: VarName -> SType t -> LExprF r t -> UExprF r t
  UFunction :: Function rt args -> LExprF r rt -> UExprF r rt
  UDensity :: Density gt args -> LExprF r EReal -> UExprF r EReal

type UExpr = SLR.IFix UExprF

instance SLR.HFunctor UExprF where
  hfmap nat = \case
    UL le -> UL $ SLR.hfmap nat le
    UIndex txt -> UIndex txt
    UIndexSize txt -> UIndexSize txt
    UVarExpr vn st e -> UVarExpr vn st $ SLR.hfmap nat e
    UFunction f e -> UFunction f $ SLR.hfmap nat e
    UDensity d e -> UDensity d $ SLR.hfmap nat e

instance SLR.HTraversable UExprF where
  htraverse nat = \case
    UL le -> UL <$> SLR.htraverse nat le
    UIndex txt -> pure $ UIndex txt
    UIndexSize txt -> pure $ UIndexSize txt
    UVarExpr vn st e -> UVarExpr vn st <$> SLR.htraverse nat e
    UFunction f e -> UFunction f <$> SLR.htraverse nat e
    UDensity d e -> UDensity d <$> SLR.htraverse nat e
  hmapM = SLR.htraverse


lExprTypeIs :: LExpr t -> SType t' -> Bool
lExprTypeIs le st = case eqLExprType le (lNamedE "" st) of
  Just Refl -> True
  Nothing -> False

eqLExpr :: LExpr ta -> LExpr tb -> Bool
eqLExpr la lb = case eqLExprType la lb of
  Just Refl -> eqLExprOf la lb
  Nothing -> False

eqSNatWith :: DT.SNatI n => DT.SNat m -> Maybe (n :~: m)
eqSNatWith sm = DT.withSNat sm DT.eqNat
eqSNat :: DT.SNat n -> DT.SNat m -> Maybe (n :~: m)
eqSNat sn sm = DT.withSNat sn $ eqSNatWith sm

{-
eqExprLists :: TestEquality r => TypedList r ts -> TypedList r ts' -> Maybe (TypedList r ts :~: TypedList r ts')
eqExprLists TL.TNil TL.TNil = Just Refl
eqExprLists (a TL.:> as) (b TL.:> bs) = do
  Refl <- testEquality a b
  Refl <- eqExprLists as bs
  pure Refl
-}
instance TestEquality LExpr where
  testEquality la lb = eqLExprType la lb

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
    go (SLR.IFix (LTuple sta)) (SLR.IFix (LTuple stb)) = do
      Refl <- testEquality sta stb
      pure Refl
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
      Refl <- eqSNat sna snb
      Refl <- go ea eb
      pure Refl
    go (SLR.IFix (LIndexedTuple sna ea)) (SLR.IFix (LIndexedTuple snb eb)) = do
      Refl <- eqSNat sna snb
      Refl <- go ea eb
      pure Refl
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
    go (SLR.IFix (LTuple tas)) (SLR.IFix (LTuple tbs)) = eqTypedLists go tas tbs
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
    go (SLR.IFix (LIndexedTuple n ea)) (SLR.IFix (LIndexedTuple m eb)) =
      case eqSNat n m of
        Nothing -> False
        Just Refl -> case eqLExprType ea eb of
          Nothing -> False
          Just Refl -> go ea eb
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
    UFunction _ le -> SLR.IFix le
    UDensity _ le -> SLR.IFix le

exprTypeIs :: UExpr t -> SType t' -> Bool
exprTypeIs ue = lExprTypeIs (uExprToSameTypeLExpr ue)
