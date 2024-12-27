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
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Stan.Language.Types.EType
  (
    module Stan.Language.Types.EType
  )
  where

import Prelude hiding (Nat)

import Data.Type.Equality ((:~:)(Refl), TestEquality(testEquality))
import Data.Type.Nat (Nat(..), SNat(..))
import Data.Type.Bool
import qualified Data.Type.Nat as DT
import Stan.Language.Recursion

import qualified GHC.TypeLits as TE
import GHC.TypeLits (ErrorMessage((:<>:)))
import qualified Text.Show
import qualified Data.GADT.Compare as GC
import qualified Data.GADT.Show as GS

import qualified Data.Text as Text

-- possible types of terms
-- NB: zero dimensional array will be treated as the underlying type
-- NB: Stan does not allow 0- or 1-Tuples. We'll enforce that in the declSpec and
-- explicit construction functions
data EType where
  EVoid :: EType
  EString :: EType
  EBool :: EType
  EInt :: EType
  EReal :: EType
  EComplex :: EType
  ECVec :: EType
  ERVec :: EType
  EMat :: EType
  ESqMat :: EType
  EArray :: Nat -> EType -> EType
  ETuple :: [EType] -> EType
--  (::->) :: EType -> EType -> EType
  deriving stock (Eq, Ord, Show)

type family ZeroDArray (e :: EType) :: EType where
  ZeroDArray (EArray (S n) _) =  TE.TypeError (TE.Text "ZeroDArray: " :<>: TE.ShowType n :<>: TE.Text " is not a zero dimensional array")
  ZeroDArray (EArray Z t) = t
  ZeroDArray t = t


type EArray1 :: EType -> EType
type EArray1 t = EArray (S Z) t

type EArray2 :: EType -> EType
type EArray2 t = EArray (S (S Z)) t

type EIndexArray :: EType
type EIndexArray = EArray1 EInt

type EIntArray :: EType
type EIntArray = EArray (S Z) EInt

type ERealArray :: EType
type ERealArray = EArray (S Z) EReal

type EComplexArray :: EType
type EComplexArray = EArray (S Z) EComplex

type E2Tuple :: EType -> EType -> EType
type E2Tuple t1 t2 = ETuple [t1, t2]

type E3Tuple :: EType -> EType -> EType -> EType
type E3Tuple t1 t2 t3 = ETuple [t1, t2, t3]

-- A mechanism to limit the types we can use in functions via a constraint
type TypeOneOf et ets = TypeOneOf' et ets (TypeMember et ets)

type family TypeOneOf' (et :: EType) (ets :: [EType]) (mem :: Bool) :: Constraint where
  TypeOneOf' et ets 'True = ()
  TypeOneOf' et ets 'False = TE.TypeError (TE.ShowType et :<>: TE.Text " is not a member of " :<>: TE.ShowType ets)

type family TypeMember (et :: EType) (ets :: [EType]) :: Bool where
  TypeMember t '[] = False
  TypeMember t (t ': ts) = True
  TypeMember t (t' ': ts) = TypeMember t ts

type family TypeSubset (ets1 :: [EType]) (ets2 :: [EType]) :: Bool where
  TypeSubset '[] _ = True
  TypeSubset (t ': ts) ts' = TypeMember t ts' && TypeSubset ts ts'


type family IfNumber (et :: EType) (a :: k) (b :: k) :: k where
  IfNumber EInt a _ = a
  IfNumber EReal a _ = a
  IfNumber EComplex a _ = a
  IfNumber _ _ b = b

type family IfRealNumber (et :: EType) (a :: k) (b :: k) :: k where
  IfRealNumber EInt a _ = a
  IfRealNumber EReal a _ = a
  IfRealNumber _ _ b = b

type family IfNumbers (a :: EType) (b :: EType) (c :: k) (d :: k) where
  IfNumbers a b c d = IfNumber a (IfNumber b c d) d

type family Promoted (a :: EType) (b :: EType) :: EType where
  Promoted a a = a
  Promoted EInt EReal = EReal
  Promoted EReal EInt = EReal
  Promoted EInt EComplex = EComplex
  Promoted EComplex EInt = EComplex
  Promoted EReal EComplex = EComplex
  Promoted EComplex EReal = EComplex
  Promoted a b = TE.TypeError (TE.Text "One of " :<>: TE.ShowType a :<>: TE.Text " and " :<>: TE.ShowType b :<>: TE.Text " isn't a promotable (number) type.")

--Stan's modifiers (e.g. "<lower=2>" apply to the internal type in an array.)
type family ScalarType (et :: EType) :: EType where
  ScalarType (EArray _ t) = ScalarType t
  ScalarType ECVec = EReal
  ScalarType ERVec = EReal
  ScalarType EMat = EReal
  ScalarType ESqMat = EReal
  ScalarType EReal = EReal
  ScalarType EInt = EInt
  ScalarType EComplex = EComplex
  ScalarType (ETuple '[]) = TE.TypeError (TE.Text "ScalarType: 0-Tuple has no scalar type and is not allowed!")
  ScalarType (ETuple '[e]) = TE.TypeError (TE.Text "ScalarType: 1-Tuple is not allowed!")
  ScalarType (ETuple es) = TE.TypeError (TE.Text "ScalarType: n-Tuple has no scalar type!")
  ScalarType a = TE.TypeError (TE.Text "ScalarType: " TE.:<>: TE.ShowType a TE.:<>: TE.Text " has no scalar type")

type family IsContainer (t :: EType) :: Constraint where
  IsContainer ECVec = ()
  IsContainer ERVec = ()
  IsContainer EMat = ()
  IsContainer ESqMat = ()
  IsContainer (EArray _ _) = ()
  IsContainer t = TE.TypeError (TE.ShowType t :<>: TE.Text " is not a container type.  Perhaps you are trying to call segment or block?")
