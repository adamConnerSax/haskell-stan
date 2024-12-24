{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
--{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}

module Stan.Language.TypedList
  (
    module Stan.Language.TypedList
  , module Stan.Language.Types
  )
  where

import Stan.Language.Types
import Stan.Language.Recursion

import Prelude hiding (Nat)
import Data.Type.Equality ((:~:)(Refl), TestEquality(testEquality))
import qualified Data.Vec.Lazy as Vec
import qualified Data.Type.Nat as DT

type family MapTypeList (f :: EType -> EType) (tl :: [EType]) :: [EType] where
  MapTypeList _ '[] = '[]
  MapTypeList f (et ': ets) = f et ': MapTypeList f ets


oneType :: SType et -> TypeList '[et]
oneType st = st ::> TypeNil


type family LastType (k :: [EType]) :: EType where
  LastType '[] = EVoid
  LastType (t ': '[]) = t
  LastType (t ': ts) = LastType ts

type family AllButLastF (k :: [EType]) (k' :: [EType]) :: [EType] where
  AllButLastF '[] '[] = '[]
  AllButLastF a (_ ': '[]) = a
  AllButLastF a (t ': ts) = AllButLastF (t ': a) ts

type family ReverseF (k :: [EType]) (k' :: [EType]):: [EType] where
  ReverseF '[] '[] = '[]
  ReverseF a '[] = a
  ReverseF a (t ': ts) = ReverseF (t ': a) ts

type family Reverse (k :: [EType]) :: [EType] where
  Reverse a = ReverseF '[] a

type family AllButLast (k :: [EType]) :: [EType] where
  AllButLast a = Reverse (AllButLastF '[] a)

type family TListLength (k :: [EType]) :: DT.Nat where
  TListLength '[] = DT.Z
  TListLength (e ': es) = DT.S (TListLength es)

type family TypeListLength (tl :: TypeList qs) :: DT.Nat where
  TypeListLength TypeNil = DT.Z
  TypeListLength (e ::> es) = DT.S (TypeListLength es)

--typeListLengthIsTListLength :: TListLength es :~: TypeListLength (TypeList es)
--typeListLengthIsTListLength = Refl

type family TypedListLength (tl :: TypedList f es) :: DT.Nat where
  TypedListLength TNil = DT.Z
  TypedListLength (a :> as) = DT.S (TypedListLength as)

typedListLength :: TypedList f es -> DT.Nat
typedListLength TNil = DT.Z
typedListLength (_ :> as) = DT.S (typedListLength as)


type family (as :: [k]) ++ (bs :: [k]) :: [k] where
  '[] ++ bs = bs
  (a ': as) ++ bs = a ': (as ++ bs)

appendTypedLists :: TypedList u as -> TypedList u bs -> TypedList u (as ++ bs)
appendTypedLists TNil b = b
appendTypedLists (a :> as) b = a :> appendTypedLists as b

--reverseTypedList :: TypedList u as -> TypedList u (Reverse as)
--reverseTypedList TNil = TNil
--reverseTypedList (a :> as) = appendTypedLists (reverseTypedList as) (a :> TNil)

zipTypedListsWith :: (forall x. a x -> b x -> c x) -> TypedList a args -> TypedList b args -> TypedList c args
zipTypedListsWith _ TNil TNil = TNil
zipTypedListsWith f (a :> as) (b :> bs) = f a b :> zipTypedListsWith f as bs

eqTypedLists :: forall (t ::EType -> Type) es. (forall a.t a -> t a -> Bool) -> TypedList t es -> TypedList t es -> Bool
eqTypedLists f a b = getAll $ mconcat $ All <$> typedKToList (zipTypedListsWith (\x y -> K $ f x y) a b)

typedKToList :: TypedList (K a) ts -> [a]
typedKToList TNil = []
typedKToList (a :> al) = unK a : typedKToList al

oneTyped :: f et -> TypedList f '[et]
oneTyped e = e :> TNil

typeListToSTypeList :: TypeList args -> TypedList SType args
typeListToSTypeList TypeNil = TNil
typeListToSTypeList (st ::> atl) = st :> typeListToSTypeList atl


applyTypedListFunctionToTypeList :: (forall u.TypedList u args -> TypedList u args') -> TypeList args -> TypeList args'
applyTypedListFunctionToTypeList f = typedSTypeListToTypeList . f . typeListToSTypeList


type family SameTypeList (e :: EType) (n :: DT.Nat) :: [EType] where
  SameTypeList _ DT.Z = '[]
  SameTypeList e (DT.S n) = e ': SameTypeList e n

class VecToSameTypedListF f (e :: EType) (n :: Nat) where
  vecToSameTypedListF :: (Nat -> a -> f e) -> Vec.Vec n a -> TypedList f (SameTypeList e n)

instance VecToSameTypedListF f e DT.Z where
  vecToSameTypedListF _ _ = TNil

instance (VecToSameTypedListF f e n) => VecToSameTypedListF f e (DT.S n) where
  vecToSameTypedListF g (v Vec.::: vs) =
    -- We use the successor here since we are using the tail to get the dictionary.
    let nt = Vec.withDict vs (DT.snatToNat $ DT.snat @(DT.S n))
    in g nt v :> vecToSameTypedListF g vs

vecToSameTypedList :: VecToSameTypedListF f e n => Vec.Vec n (f e) -> TypedList f (SameTypeList e n)
vecToSameTypedList = vecToSameTypedListF (const id)


class SameTypedListToVecF (f :: EType -> Type) (e :: EType) (n :: Nat) where
  sameTypedListToVecF :: (f e -> a) -> TypedList f (SameTypeList e n) -> Vec.Vec n a

instance SameTypedListToVecF f e DT.Z where
  sameTypedListToVecF _ _ = Vec.VNil

instance (SameTypedListToVecF f e n) => SameTypedListToVecF f e (DT.S n) where
  sameTypedListToVecF g (e :> es) = g e Vec.::: sameTypedListToVecF g es

sameTypedListToVec :: SameTypedListToVecF f e n => TypedList f (SameTypeList e n) -> Vec.Vec n (f e)
sameTypedListToVec = sameTypedListToVecF id




{-
sameTypedListToVec :: TypedList f (SameTypeList e n) -> Vec.Vec n (f e)
sameTypedListToVec stl = go stl Vec.VNil
  where
    go :: TypedList f (SameTypeList e l) -> Vec.Vec m (f e) -> Vec.Vec (l `DT.Plus` m) (f e)
    go TNil v = v
    go (al :> als) v = go als (al Vec.::: v)
-}

{-
type family VTTL (e :: EType) (n :: Nat) (es :: [EType]) :: [EType] where
  VTTL _ DT.Z es = es
  VTTL e (DT.S n) es = VTTL e n (e ': es)
-}
--type SameTypeList (e :: EType) (n :: Nat) = VTTL e n '[]

--stSuc :: (n :~: TypeListLength (SameTypeList e n)) -> (DT.S n :~: TypeListLength (SameTypeList e (DT.S n)))
--stSuc proofN = case proofN of
--  Just Refl ->


{-
vecToTypedList' :: forall f e n . Vec.Vec n (f e) -> TypedList f (SameTypeList e n)
vecToTypedList' v = go v (TNil :: TypedList f (SameTypeList e DT.Z)) where
  go :: Vec.Vec m (f e) -> TypedList f (SameTypeList e l) -> TypedList f (SameTypeList e (l `DT.Plus` m))
  go Vec.VNil tl = tl
  go (fe Vec.::: fes) tl = go fes (fe :> tl)
-}
{-
vecToTypedList :: Vec.Vec n (f e) -> TypedList f (SameTypeList e n)
vecToTypedList v = go v TNil where
  go :: Vec.Vec m (f e) -> TypedList f ds -> TypedList f (VTTL e m ds)
  go Vec.VNil tl = tl
  go (fe Vec.::: fes) tl = go fes (fe :> tl)
-}
--proveSTLZ :: (SameTypeList e n :~: '[]) -> (n :~: DT.Z)
--proveSTLZ p = case p of
--  Just Refl ->
{-
class VecToSameTypedList (f :: EType -> Type) (e :: EType) (n :: Nat) where
  vecToSameTypedList :: Vec.Vec n (f e) -> TypedList f (SameTypeList e n)

instance VecToSameTypedList f e DT.Z where
  vecToSameTypedList _ = TNil

instance (VecToSameTypedList f e n) => VecToSameTypedList f e (DT.S n) where
  vecToSameTypedList (v Vec.::: vs) = v :> vecToSameTypedList vs
-}
