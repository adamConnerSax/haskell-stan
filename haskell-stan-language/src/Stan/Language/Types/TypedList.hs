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
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Stan.Language.Types.TypedList
  (
    module Stan.Language.Types.TypedList
  )
  where

import qualified Stan.Language.Types.EType as SLTE
import qualified Stan.Language.Recursion as SLR

import qualified Data.Type.Nat as DTN
import qualified Data.Vec.Lazy as Vec

import Data.Type.Equality ((:~:)(Refl), TestEquality(testEquality))

-- list of arguments.  Parameterized by an expression type and the list of arguments
data TypedList ::  (SLTE.EType -> Type) -> [SLTE.EType] -> Type where
  TNil :: TypedList f '[]
  (:>) :: f et -> TypedList f ets -> TypedList f (et ': ets)

infixr 2 :>

instance TestEquality a => TestEquality (TypedList a) where
  testEquality TNil TNil = Just Refl
  testEquality (sta :> as) (stb :> bs) = do
    Refl <- testEquality sta stb
    Refl <- testEquality as bs
    pure Refl
  testEquality _ _ = Nothing

instance SLR.HFunctor TypedList where
  hfmap nat = \case
    TNil -> TNil
    (:>) g al -> nat g :> SLR.hfmap nat al

instance SLR.HTraversable TypedList where
  htraverse natM = \case
    TNil -> pure TNil
    (:>) aet al -> (:>) <$> natM aet <*> SLR.htraverse natM al
  hmapM = SLR.htraverse


eqTypedList :: forall f es es' . TestEquality f => TypedList f es -> TypedList f es' -> Bool
eqTypedList = go
  where
    go :: TypedList f as -> TypedList f as' -> Bool
    go TNil TNil = True
    go (sta :> as) (stb :> bs) = case testEquality sta stb of
      Just Refl -> go as bs
      Nothing -> False
    go _ _ = False

withTypedList ::  (forall t . f t -> a) -> TypedList f args -> [a]
withTypedList _ TNil = []
withTypedList f (st :> ats) = f st : withTypedList f ats

foldTypedList :: forall a b ts . (forall x. a x -> b -> b) -> b -> TypedList a ts -> b
foldTypedList f = go
  where
    go :: forall ts' . b -> TypedList a ts' -> b
    go b TNil = b
    go b (a :> as) = go (f a b) as

type family TypedListLength (tl :: TypedList f qs) :: DTN.Nat where
  TypedListLength TNil  = DTN.Z
  TypedListLength (_ :> es) = DTN.S (TypedListLength es)

typedListLength :: TypedList f es -> DTN.Nat
typedListLength TNil = DTN.Z
typedListLength (_ :> as) = DTN.S (typedListLength as)


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

eqTypedLists :: forall (t ::SLTE.EType -> Type) es. (forall a.t a -> t a -> Bool) -> TypedList t es -> TypedList t es -> Bool
eqTypedLists f a b = getAll $ mconcat $ All <$> typedKToList (zipTypedListsWith (\x y -> SLR.K $ f x y) a b)

typedKToList :: TypedList (SLR.K a) ts -> [a]
typedKToList TNil = []
typedKToList (a :> al) = SLR.unK a : typedKToList al

oneTyped :: f et -> TypedList f '[et]
oneTyped e = e :> TNil

--applyTypedListFunctionToSTypeList :: (forall u.TypedList u args -> TypedList u args') -> TypeList args -> TypeList args'
--applyTypedListFunctionToSTypeList f = typedSTypeListToTypeList . f . typeListToSTypeList

type family SameTypeList (e :: SLTE.EType) (n :: DTN.Nat) :: [SLTE.EType] where
  SameTypeList _ DTN.Z = '[]
  SameTypeList e (DTN.S n) = e ': SameTypeList e n

--instance GenSType e => AllGenSTypes (SameTypeList e n) where


class VecToSameTypedListF f (e :: SLTE.EType) (n :: DTN.Nat) where
  vecToSameTypedListF :: (DTN.Nat -> a -> f e) -> Vec.Vec n a -> TypedList f (SameTypeList e n)

instance VecToSameTypedListF f e DTN.Z where
  vecToSameTypedListF _ _ = TNil

instance (VecToSameTypedListF f e n) => VecToSameTypedListF f e (DTN.S n) where
  vecToSameTypedListF g (v Vec.::: vs) =
    -- We use the successor here since we are using the tail to get the dictionary.
    let nt = Vec.withDict vs (DTN.snatToNat $ DTN.snat @(DTN.S n))
    in g nt v :> vecToSameTypedListF g vs

vecToSameTypedList :: VecToSameTypedListF f e n => Vec.Vec n (f e) -> TypedList f (SameTypeList e n)
vecToSameTypedList = vecToSameTypedListF (const id)

class SameTypedListToVecF (f :: SLTE.EType -> Type) (e :: SLTE.EType) (n :: DTN.Nat) where
  sameTypedListToVecF :: (f e -> a) -> TypedList f (SameTypeList e n) -> Vec.Vec n a

instance SameTypedListToVecF f e DTN.Z where
  sameTypedListToVecF _ _ = Vec.VNil

instance (SameTypedListToVecF f e n) => SameTypedListToVecF f e (DTN.S n) where
  sameTypedListToVecF g (e :> es) = g e Vec.::: sameTypedListToVecF g es

sameTypedListToVec :: SameTypedListToVecF f e n => TypedList f (SameTypeList e n) -> Vec.Vec n (f e)
sameTypedListToVec = sameTypedListToVecF id
