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
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module Stan.Language.TypedList
  (
    module Stan.Language.TypedList
  )
  where

import Stan.Language.Types
import Stan.Language.Recursion

import Prelude hiding (Nat)
import Data.Type.Equality ((:~:)(Refl), TestEquality(testEquality))
import qualified Data.Vec.Lazy as Vec
import qualified Data.Type.Nat as DT

-- singleton for a list of arguments
data TypeList :: [EType] -> Type where
  TypeNil :: TypeList '[]
  (::>) :: SType et -> TypeList ets -> TypeList (et ': ets)

infixr 2 ::>

type family MapTypeList (f :: EType -> EType) (tl :: [EType]) :: [EType] where
  MapTypeList _ '[] = '[]
  MapTypeList f (et ': ets) = f et ': MapTypeList f ets


instance TestEquality TypeList where
  testEquality TypeNil TypeNil = Just Refl
  testEquality (sta ::> as) (stb ::> bs) = do
    Refl <- testEquality sta stb
    Refl <- testEquality as bs
    pure Refl
  testEquality _ _ = Nothing

eqTypeList :: TypeList es -> TypeList es' -> Bool
eqTypeList = go
  where
    go :: TypeList es -> TypeList es' -> Bool
    go TypeNil TypeNil = True
    go (sta ::> as) (stb ::> bs) = case testEquality sta stb of
      Just Refl -> go as bs
      Nothing -> False
    go _ _ = False

typesToList ::  (forall t.SType t -> a) -> TypeList args -> [a]
typesToList _ TypeNil = []
typesToList f (st ::> ats) = f st : typesToList f ats

typeListToTypedListOfTypes :: TypeList args -> TypedList SType args
typeListToTypedListOfTypes TypeNil = TNil
typeListToTypedListOfTypes (st ::> atl) = st :> typeListToTypedListOfTypes atl

oneType :: SType et -> TypeList '[et]
oneType st = st ::> TypeNil

class GenTypeList (ts :: [EType]) where
  genTypeList :: TypeList ts

instance GenTypeList '[] where
  genTypeList = TypeNil

instance (GenSType t, GenTypeList ts) => GenTypeList (t ': ts)  where
  genTypeList = genSType @t ::> genTypeList @ts

type family AllGenTypes (ts :: [EType]) :: Constraint where
  AllGenTypes '[] = ()
  AllGenTypes (t ': ts) = (GenSType t, AllGenTypes ts)

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

-- list of arguments.  Parameterized by an expression type and the list of arguments
data TypedList ::  (EType -> Type) -> [EType] -> Type where
  TNil :: TypedList f '[]
  (:>) :: f et -> TypedList f ets -> TypedList f (et ': ets)

infixr 2 :>

type family TypedListLength (tl :: TypedList f es) :: DT.Nat where
  TypedListLength TNil = DT.Z
  TypedListLength (a :> as) = DT.S (TypedListLength as)

typedListLength :: TypedList f es -> DT.Nat
typedListLength TNil = DT.Z
typedListLength (_ :> as) = DT.S (typedListLength as)

instance HFunctor TypedList where
  hfmap nat = \case
    TNil -> TNil
    (:>) g al -> nat g :> hfmap nat al

instance HTraversable TypedList where
  htraverse natM = \case
    TNil -> pure TNil
    (:>) aet al -> (:>) <$> natM aet <*> htraverse natM al
  hmapM = htraverse

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

-- This is fun! Fold a typed list using a function of it's held data and the coresponding STypes
foldTypedList :: forall a b ts . AllGenTypes ts => (forall x. a x -> SType x -> b -> b) -> b -> TypedList a ts -> b
foldTypedList f = go
  where
    go :: forall ts' . AllGenTypes ts' => b -> TypedList a ts' -> b
    go b TNil = b
    go b (a :> as) = go (f a genSType b) as

--typeChangingMap :: (forall t. u t -> u (F t')) -> TypedList u as ->

eqTypedLists :: forall (t ::EType -> Type) es. (forall a.t a -> t a -> Bool) -> TypedList t es -> TypedList t es -> Bool
eqTypedLists f a b = getAll $ mconcat $ All <$> typedKToList (zipTypedListsWith (\x y -> K $ f x y) a b)

{-
eqArgLists :: forall (t ::EType -> Type) es es'. (forall a.t a -> t a -> Bool) -> ArgList t es -> ArgList t es' -> Bool
eqArgLists f = go
  where
    go :: ArgList t ls -> ArgList t ls' -> Bool
    go ArgNil ArgNil = True
    go (x :> xs) (y :> ys) = f x y && go xs ys
-}

typedKToList :: TypedList (K a) ts -> [a]
typedKToList TNil = []
typedKToList (a :> al) = unK a : typedKToList al

oneTyped :: f et -> TypedList f '[et]
oneTyped e = e :> TNil

typeListToSTypeList :: TypeList args -> TypedList SType args
typeListToSTypeList TypeNil = TNil
typeListToSTypeList (st ::> atl) = st :> typeListToSTypeList atl

typedSTypeListToTypeList :: TypedList SType args -> TypeList args
typedSTypeListToTypeList TNil = TypeNil
typedSTypeListToTypeList (st :> xs) = st ::> typedSTypeListToTypeList xs

applyTypedListFunctionToTypeList :: (forall u.TypedList u args -> TypedList u args') -> TypeList args -> TypeList args'
applyTypedListFunctionToTypeList f = typedSTypeListToTypeList . f . typeListToSTypeList

class GenTypedList (ts :: [EType]) where
  genTypedList :: TypedList SType ts

instance GenTypedList '[] where
  genTypedList = TNil

instance (GenSType t, GenTypedList ts) => GenTypedList (t ': ts)  where
  genTypedList = genSType @t :> genTypedList @ts

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
