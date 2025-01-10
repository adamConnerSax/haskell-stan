{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}

module Stan.Language.Indexing
  ( module Stan.Language.Indexing,
    Fin (..),
    Vec (..)
  )
where

import Data.Fin (Fin (..))
import Data.Type.Nat (Nat(..), SNat(..))
import qualified Data.Type.Nat as DTN
import Data.Vec.Lazy (Vec (..))
import qualified Data.Vec.Lazy as DVL
import qualified GHC.TypeLits as TE
import qualified Stan.Language.Recursion as TR
import qualified Stan.Language.Types as SLT
import Prelude hiding (Nat)
import Data.Type.Equality ((:~:)(Refl), TestEquality(testEquality))
import Type.Reflection (typeRep)

-- to simplify most indexing
-- term level
n0 :: Nat = Z

n1 :: Nat = S Z

n2 :: Nat = S n1

n3 :: Nat = S n2

-- type level
type N0 :: Nat
type N0 = Z

type N1 :: Nat
type N1 = S Z

type N2 :: Nat
type N2 = S (S Z)

type N3 :: Nat
type N3 = S (S (S Z))

s0 :: SNat Z = SZ

s1 :: SNat (S Z) = SS

s2 :: SNat (S (S Z)) = SS

s3 :: SNat (S (S (S Z))) = SS

s4 :: SNat (S (S (S (S Z)))) = SS

-- popRandom :: forall n m a. (DT.SNatI n, DT.SNatI m) => Vec (DT.Plus n (S m)) a -> (a, Vec (DT.Plus n m) a)
-- popRandom v = (a, vL DT.++ vR)
--  where (vL, a ::: vR) = DT.split v :: (Vec n a, Vec (S m) a)

type family IndexedTuple (n :: Nat) (e :: SLT.EType) :: SLT.EType where
  IndexedTuple _ (SLT.ETuple '[]) = TE.TypeError (TE.Text "Cannot index a 0-tuple. Did you index an n-tuple at a position > n?")
  IndexedTuple Z (SLT.ETuple '[e] ) = e
  IndexedTuple Z (SLT.ETuple (e ': _)) = e
  IndexedTuple (S n) (SLT.ETuple (e ': es)) = IndexedTuple n (SLT.ETuple es)

data DiffHolder = PosDiff Nat | Same | NegDiff Nat

type family Diff (n :: Nat) (m :: Nat) :: DiffHolder where
  Diff Z Z = Same
  Diff (S n) Z = PosDiff (S n)
  Diff Z (S n) = NegDiff (S n) --TE.TypeError (TE.Text "Diff: attempt to take diff of m and n where n is larger than m.")
  Diff (S n) (S m) = Diff n m

type family DeclDimension (e :: SLT.EType) :: Nat where
  DeclDimension SLT.EInt = Z
  DeclDimension SLT.EReal = Z
  DeclDimension SLT.EComplex = Z
  DeclDimension SLT.ECVec = S Z
  DeclDimension SLT.ERVec = S Z
  DeclDimension SLT.EMat = S (S Z)
  DeclDimension SLT.ESqMat = S Z
  DeclDimension (SLT.EArray n t) = n `DTN.Plus` DeclDimension t
  DeclDimension a = Z -- TE.TypeError (TE.Text "DeclDimension: " TE.:<>: TE.ShowType a TE.:<>: TE.Text " has no well-defined idea of declared dimension")

type family Dimension (e :: SLT.EType) :: Nat where
  Dimension SLT.EInt = Z
  Dimension SLT.EReal = Z
  Dimension SLT.EComplex = Z
  Dimension SLT.ECVec = S Z
  Dimension SLT.ERVec = S Z
  Dimension SLT.EMat = S (S Z)
  Dimension SLT.ESqMat = S (S Z)
  Dimension (SLT.EArray n t) = n `DTN.Plus` Dimension t
  Dimension a = TE.TypeError (TE.Text "Dimension: " TE.:<>: TE.ShowType a TE.:<>: TE.Text " has no well-defined idea of dimension")

type family ApplyDiffToEType (n :: DiffHolder) (e :: SLT.EType) :: SLT.EType where
  ApplyDiffToEType _ (SLT.EArray Z t) = TE.TypeError (TE.Text "Attempt to slice a zero-dimensional array.  Which means you had a zero dimensional array?")
  ApplyDiffToEType (PosDiff _) (SLT.EArray (S Z) t) = TE.TypeError (TE.Text "ApplyDiffToEType: Impossible case of PosDiff but array of dimension 1.")
--  ApplyDiffToEType (PosDiff _) (EArray (S Z) t) = t -- slice is in the array
  ApplyDiffToEType (PosDiff _) (SLT.EArray (S n) t) = SLT.EArray n t -- slice is in the array
  ApplyDiffToEType Same (SLT.EArray (S Z) t) = t -- Slice a 1-d array case.
  ApplyDiffToEType Same (SLT.EArray (S n) t) = SLT.EArray n t
--  ApplyDiffToEType (NegDiff (S n)) (EArray o t) = EArray o (Sliced n t) -- array doesn not have enough dimensions.  Slice the rest from the contained type.
  ApplyDiffToEType (NegDiff (S n)) (SLT.EArray o t) = Sliced n t -- array doesn not have enough dimensions.  Slice the rest from the contained type.
  ApplyDiffToEType _ x = TE.TypeError (TE.Text "ApplyDiffToEtype to type other than EArray.")

type family Sliced (n :: Nat) (a :: SLT.EType) :: SLT.EType where
  Sliced _ SLT.EInt = TE.TypeError (TE.Text "Cannot slice (index) a scalar int.")
  Sliced _ SLT.EReal = TE.TypeError (TE.Text "Cannot slice (index) a scalar real.")
  Sliced _ SLT.EComplex = TE.TypeError (TE.Text "Cannot slice (index) a scalar complex.")
  Sliced Z SLT.ERVec = SLT.EReal
  Sliced _ SLT.ERVec = TE.TypeError (TE.Text "Cannot slice (index) a row-vector at a position other than 0.")
  Sliced Z SLT.ECVec = SLT.EReal
  Sliced _ SLT.ECVec = TE.TypeError (TE.Text "Cannot slice (index) a vector at a position other than 0.")
--  Sliced Z ESimplex = EReal
--  Sliced _ ESimplex = TE.TypeError (TE.Text "Cannot slice (index) a simplex at a position other than 0.")
  Sliced Z SLT.EMat = SLT.ERVec
  Sliced (S Z) SLT.EMat = SLT.ECVec
  Sliced _ SLT.EMat = TE.TypeError (TE.Text "Cannot slice (index) a matrix at a position other than 0 or 1.")
  Sliced Z SLT.ESqMat = SLT.ERVec
  Sliced (S Z) SLT.ESqMat = SLT.ECVec
  Sliced _ SLT.ESqMat = TE.TypeError (TE.Text "Cannot slice (index) a matrix at a position other than 0 or 1.")
  Sliced n (SLT.EArray n t) = t
  Sliced n (SLT.EArray m t) = ApplyDiffToEType (Diff m (S n)) (SLT.EArray m t)

type family SliceInnerN (n :: Nat) (a :: SLT.EType) :: SLT.EType where
--  SliceInnerN Z (EArray Z a) = a
  SliceInnerN Z a = a
  SliceInnerN (S n) a = SliceInnerN n (Sliced Z a)

{-
fullArraySliceProof1 :: SliceInnerN (S Z) (EArray (S Z) t) :~: t
fullArraySliceProof1 = Refl

fullArraySliceProofI :: forall n t .
                        (SliceInnerN n (EArray n t) :~: t) -> (SliceInnerN (S n) (EArray (S n) t) :~: t)
fullArraySliceProofI pn = case pn of
  Refl ->
-}

type family IfLessOrEq (n :: Nat) (m :: Nat) (a :: SLT.EType) (b :: SLT.EType) :: SLT.EType where
  IfLessOrEq Z Z a _ = a
  IfLessOrEq Z (S n) a _ = a
  IfLessOrEq (S n) Z _ b = b
  IfLessOrEq (S n) (S m) a b = IfLessOrEq n m a b

-- test if the expression can be indexed at the dimension n
-- if so, return the expression, otherwise, error
-- What's going on w square matrix??
type family Indexed (n :: Nat) (a :: SLT.EType) :: SLT.EType where
--  Indexed Z ESimplex = ESimplex
--  Indexed _ ESimplex = TE.TypeError (TE.Text "Attempt to index a simplex at a position other than 0.")
  Indexed Z SLT.ECVec = SLT.ECVec
  Indexed _ SLT.ECVec = TE.TypeError (TE.Text "Attempt to index a vector at a position other than 0.")
  Indexed Z SLT.ERVec = SLT.ERVec
  Indexed _ SLT.ERVec = TE.TypeError (TE.Text "Attempt to index a row_vector at a position other than 0.")
  Indexed Z SLT.EMat = SLT.EMat
  Indexed (S Z) SLT.EMat = SLT.EMat
  Indexed _ SLT.EMat = TE.TypeError (TE.Text "Attempt to index a matrix at a position other than 0 or 1.")
  Indexed Z SLT.ESqMat = SLT.EMat
  Indexed (S Z) SLT.ESqMat = SLT.EMat
  Indexed _ SLT.ESqMat = TE.TypeError (TE.Text "Attempt to index a (square) matrix at a position other than 0 or 1.")
  Indexed n (SLT.EArray m t) = IfLessOrEq (S n) (Dimension (SLT.EArray m t)) (SLT.EArray m t) (TE.TypeError (TE.Text "Attempt to index an array at too high an index."))
  Indexed _ _ = TE.TypeError (TE.Text "Cannot index a scalar.")

newtype DeclIndexVecF (r :: SLT.EType -> Type) (et :: SLT.EType) = DeclIndexVecF {unDeclIndexVecF :: Vec (DeclDimension et) (r SLT.EInt) }

instance TR.HFunctor DeclIndexVecF where
  hfmap nat (DeclIndexVecF v) = DeclIndexVecF $ DVL.map nat v

instance TR.HTraversable DeclIndexVecF where
  hmapM natM = fmap DeclIndexVecF . traverse natM . unDeclIndexVecF
  htraverse natM = fmap DeclIndexVecF . traverse natM . unDeclIndexVecF

newtype IndexVecF (r :: SLT.EType -> Type) (et :: SLT.EType) = IndexVecF {unIndexVecF :: Vec (Dimension et) (r SLT.EInt)}

instance TR.HFunctor IndexVecF where
  hfmap nat (IndexVecF v) = IndexVecF $ DVL.map nat v

instance TR.HTraversable IndexVecF where
  hmapM natM = fmap IndexVecF . traverse natM . unIndexVecF
  htraverse natM = fmap IndexVecF . traverse natM . unIndexVecF

newtype IndexVecM (r :: SLT.EType -> Type) (et :: SLT.EType) = IndexVecM {unIndexVecM :: Vec (Dimension et) (Maybe (r SLT.EInt)) }

instance TR.HFunctor IndexVecM where
  hfmap nat (IndexVecM v) = IndexVecM $ DVL.map (fmap nat) v

instance TR.HTraversable IndexVecM where
  htraverse natM = fmap IndexVecM . traverse (traverse natM) . unIndexVecM
  hmapM = TR.htraverse

data NestedVec :: Nat -> Type -> Type where
  NestedVec1 :: Vec (S n) a -> NestedVec (S Z) a
  NestedVec2 :: Vec (S n) (Vec (S m) a) -> NestedVec (S (S Z)) a
  NestedVec3 :: Vec (S n) (Vec (S m) (Vec (S k) a)) -> NestedVec (S (S (S Z))) a

instance Functor (NestedVec n) where
  fmap f = \case
    NestedVec1 v -> NestedVec1 $ DVL.map f v
    NestedVec2 v -> NestedVec2 $ DVL.map (DVL.map f) v
    NestedVec3 v -> NestedVec3 $ DVL.map (DVL.map (DVL.map f)) v

instance Foldable (NestedVec n) where
  foldMap f = \case
    NestedVec1 v -> foldMap f v
    NestedVec2 v -> mconcat $ DVL.toList $ fmap (foldMap f) v
    NestedVec3 v -> mconcat $ concatMap DVL.toList $ DVL.toList $ fmap (foldMap f) <$> v

instance Traversable (NestedVec n) where
  traverse f = \case
    NestedVec1 v -> NestedVec1 <$> DVL.traverse f v
    NestedVec2 v -> NestedVec2 <$> DVL.traverse (DVL.traverse f) v
    NestedVec3 v -> NestedVec3 <$> DVL.traverse (DVL.traverse (DVL.traverse f)) v

nestedVecHead :: NestedVec n a -> a
nestedVecHead (NestedVec1 (a ::: _)) = a
nestedVecHead (NestedVec2 ((a ::: _) ::: _)) = a
nestedVecHead (NestedVec3 (((a ::: _) ::: _) ::: _)) = a

eqSizeNestedVec :: NestedVec n a -> NestedVec m b -> Maybe (n :~: m)
eqSizeNestedVec (NestedVec1 _) (NestedVec1 _) = Just Refl
eqSizeNestedVec (NestedVec2 _) (NestedVec2 _) = Just Refl
eqSizeNestedVec (NestedVec3 _) (NestedVec3 _) = Just Refl
eqSizeNestedVec _ _ = Nothing

eqNestedVec :: (a -> a -> Bool) -> NestedVec n a -> NestedVec n a -> Bool
eqNestedVec f nva nvb =
  let (sa, eltsA) = unNest nva
      (sb, eltsB) = unNest nvb
      eltsSame = getAll $ mconcat $ All <$> zipWith f eltsA eltsB
  in sa == sb && eltsSame

eqVecLength :: Vec n a -> Vec m b -> Maybe (n :~: m)
eqVecLength = go
  where
    go :: forall n m a b.Vec n a -> Vec m b -> Maybe (n :~: m)
    go VNil VNil = Just Refl
    go (_ ::: as) (_ ::: bs) = case go as bs of
      Just Refl -> Just Refl
      Nothing -> Nothing
    go _ _ = Nothing

eqVecEltType :: forall a b m n.(Typeable a, Typeable b) => Vec n a -> Vec m b -> Maybe (a :~: b)
eqVecEltType _ _ = testEquality (typeRep @a) (typeRep @b)

eqVec :: (Typeable a, Typeable b, Eq a) => Vec n a -> Vec m b -> Bool
eqVec v1 v2 = case eqVecLength v1 v2 of
  Just Refl -> case eqVecEltType v1 v2 of
    Just Refl -> DVL.toList v1 == DVL.toList v2
    Nothing -> False
  Nothing -> False


unNest :: NestedVec n a -> ([Int], [a])
unNest (NestedVec1 v) = ([DVL.length v], DVL.toList v)
unNest (NestedVec2 v) = ([DVL.length v, DVL.length (DVL.head v)], concatMap DVL.toList $ DVL.toList v)
unNest (NestedVec3 v) = ([DVL.length v, DVL.length (DVL.head v), DVL.length (DVL.head (DVL.head v))], concat $ concatMap (fmap DVL.toList . DVL.toList) (DVL.toList v))

{-
eTypeDim :: SType e -> Nat
eTypeDim = \case
  SInt -> n0
  SReal -> n0
  SComplex -> n0
  SCVec -> n1
  SRVec -> n1
  SMat -> n2
  SSqMat -> n2
  SArray sn st -> DT.snatToNat sn + eTypeDim st
  SBool -> n0
-}
