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

module Stan.Language.Types.STypeList
  (
    module Stan.Language.Types.STypeList
  )
  where

import Prelude hiding (Nat)

import qualified Stan.Language.Types.EType as SLTE
import qualified Stan.Language.Types.SType as SLTS
import qualified Stan.Language.Types.TypedList as SLTT

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
