{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Stan.ModelBuilder.TypedExpressions.Indexing
  (
    module Stan.ModelBuilder.TypedExpressions.Indexing
  , Fin(..)
  , Vec(..)
  )
  where

import qualified Stan.ModelBuilder.TypedExpressions.Recursion as TR
import Stan.ModelBuilder.TypedExpressions.Types

import Prelude hiding (Nat)
import           Data.Kind (Type)

import Data.Fin (Fin(..))
import Data.Vec.Lazy (Vec(..))

import qualified Data.Type.Nat as DT
import qualified Data.Vec.Lazy as DT

import qualified GHC.TypeLits as TE
import GHC.TypeLits (ErrorMessage((:<>:)))

-- to simplify most indexing
n0 :: Nat = Z
n1 :: Nat = S Z
n2 :: Nat = S n1
n3 :: Nat = S n2


-- to simplify most indexing
i0 :: SNat Z = DT.SZ
i1 :: SNat (S Z) = DT.SS
i2 :: SNat (S (S Z)) = DT.SS
i3 :: SNat (S (S (S Z))) = DT.SS

popRandom :: forall n m a. (DT.SNatI n, DT.SNatI m) => Vec (DT.Plus n (S m)) a -> (a, Vec (DT.Plus n m) a)
popRandom v = (a, vL DT.++ vR)
  where (vL, a ::: vR) = DT.split v :: (Vec n a, Vec (S m) a)

type family DiffOrZero (n :: Nat) (m :: Nat) :: Nat where
  DiffOrZero Z Z = Z
  DiffOrZero (S n) Z = S n
  DiffOrZero Z (S m) = Z
  DiffOrZero (S n) (S m) = DiffOrZero n m

type family DeclDimension (e :: EType) :: Nat where
  DeclDimension EInt = Z
  DeclDimension EReal = Z
  DeclDimension EComplex = Z
  DeclDimension ECVec = S Z
  DeclDimension ERVec = S Z
  DeclDimension EMat  = S (S Z)
  DeclDimension ESqMat = S Z
  DeclDimension (EArray n t) = n `DT.Plus` Dimension t

type family Dimension (e :: EType) :: Nat where
  Dimension EInt = Z
  Dimension EReal = Z
  Dimension EComplex = Z
  Dimension ECVec = S Z
  Dimension ERVec = S Z
  Dimension EMat = S (S Z)
  Dimension ESqMat = S (S Z)
  Dimension (EArray n t) = n `DT.Plus` Dimension t

type family ApplyDiffOrZeroToEType (n :: Nat) (e :: EType) :: EType where
  ApplyDiffOrZeroToEType Z (EArray Z t) = t
  ApplyDiffOrZeroToEType Z (EArray (S n) t) = EArray n t
  ApplyDiffOrZeroToEType d (EArray m t) = EArray m (Sliced d t)
  ApplyDiffOrZeroToEType _ x = x

type family Sliced (n :: Nat) (a :: EType) :: EType where
  Sliced _ EInt = TE.TypeError (TE.Text "Cannot slice (index) a scalar int.")
  Sliced _ EReal = TE.TypeError (TE.Text "Cannot slice (index) a scalar real.")
  Sliced _ EComplex = TE.TypeError (TE.Text "Cannot slice (index) a scalar complex.")
  Sliced Z ERVec = EReal
  Sliced _ ERVec = TE.TypeError (TE.Text "Cannot slice (index) a row-vector at a position other than 0.")
  Sliced Z ECVec = EReal
  Sliced _ ECVec = TE.TypeError (TE.Text "Cannot slice (index) a vector at a position other than 0.")
  Sliced _ ERVec = TE.TypeError (TE.Text "Cannot slice (index) a vector at a position other than 0.")
  Sliced Z EMat = ERVec
  Sliced (S Z) EMat = ECVec
  Sliced _ EMat = TE.TypeError (TE.Text "Cannot slice (index) a matrix at a position other than 0 or 1.")
  Sliced Z ESqMat = ERVec
  Sliced (S Z) ESqMat = ECVec
  Sliced _ ESqMat = TE.TypeError (TE.Text "Cannot slice (index) a matrix at a position other than 0 or 1.")
  Sliced n (EArray m t) = ApplyDiffOrZeroToEType (DiffOrZero m n) (EArray m t)

type family SliceInnerN (n :: Nat) (a :: EType) :: EType where
  SliceInnerN Z a = a
  SliceInnerN (S n) a = SliceInnerN n (Sliced Z a)


newtype DeclIndexVecF (s :: EStructure)(r :: Ty -> Type) (et :: EType) = DeclIndexVecF { unDeclIndexVecF :: Vec (DeclDimension et) (r ('Ty s EInt))}

instance TR.NFunctor (DeclIndexVecF s) where
  nmap nat (DeclIndexVecF v) = DeclIndexVecF $ DT.map nat v



newtype IndexVecF (s :: EStructure) (r :: Ty -> Type) (et :: EType) = IndexVecF { unIndexVecF :: Vec (Dimension et) (r ('Ty s EInt)) }

instance TR.NFunctor (IndexVecF s) where
  nmap nat (IndexVecF v) = IndexVecF $ DT.map nat v