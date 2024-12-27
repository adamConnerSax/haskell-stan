{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}

module Stan.Language.Types.ETypeList
  (
    module Stan.Language.Types.ETypeList
  )
  where

import qualified Stan.Language.Types.EType as SLTE

import Prelude hiding (Nat)
import qualified Data.Type.Nat as DT

type family MapTypeList (f :: SLTE.EType -> SLTE.EType) (tl :: [SLTE.EType]) :: [SLTE.EType] where
  MapTypeList _ '[] = '[]
  MapTypeList f (et ': ets) = f et ': MapTypeList f ets


type family LastType (k :: [SLTE.EType]) :: SLTE.EType where
  LastType '[] = SLTE.EVoid
  LastType (t ': '[]) = t
  LastType (t ': ts) = LastType ts

type family AllButLastF (k :: [SLTE.EType]) (k' :: [SLTE.EType]) :: [SLTE.EType] where
  AllButLastF '[] '[] = '[]
  AllButLastF a (_ ': '[]) = a
  AllButLastF a (t ': ts) = AllButLastF (t ': a) ts

type family ReverseF (k :: [SLTE.EType]) (k' :: [SLTE.EType]):: [SLTE.EType] where
  ReverseF '[] '[] = '[]
  ReverseF a '[] = a
  ReverseF a (t ': ts) = ReverseF (t ': a) ts

type family Reverse (k :: [SLTE.EType]) :: [SLTE.EType] where
  Reverse a = ReverseF '[] a

type family AllButLast (k :: [SLTE.EType]) :: [SLTE.EType] where
  AllButLast a = Reverse (AllButLastF '[] a)

type family TListLength (k :: [SLTE.EType]) :: DT.Nat where
  TListLength '[] = DT.Z
  TListLength (e ': es) = DT.S (TListLength es)
