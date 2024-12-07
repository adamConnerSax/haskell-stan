{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImpredicativeTypes #-}
--{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Stan.Functions.Constraints
  (
    module Stan.Functions.Constraints
  , module Stan.Language.Types -- reexport the constraints
  , module Stan.Language.Indexing
  )
  where

import qualified Stan.Language.Types as SLT
import qualified Stan.Language.Indexing as SLI
import Stan.Language.Types (TypeOneOf, GenSType, IsContainer)
import Stan.Language.Indexing (Dimension)
--import Stan.Language.TypedList (TypedList(..))
--import GHC.TypeLits (ErrorMessage((:<>:)))
--import Data.Type.Nat (SNatI)
--import Data.Type.Equality (type (~))
import Prelude hiding (Nat)

-- this needs fixing for higher dimensions?
type VectorizedReal t = (SLT.GenSType t, SLT.ScalarType t ~ SLT.EReal)
type ArrayOf t = forall n . SLT.EArray n t
type RealContainer t = (SLT.GenSType t, SLT.ScalarType t ~ SLT.EReal, SLT.TypeOneOf t [SLT.ECVec, SLT.ERVec, SLT.EMat, SLT.ESqMat, ArrayOf SLT.EReal])
type Vectorable t = (SLT.TypeOneOf t [SLT.EReal, SLT.ECVec, SLT.ERVec, SLT.EArray1 SLT.EInt, SLT.EArray1 SLT.EReal, SLT.EMat, SLT.ESqMat], SLT.GenSType t)
type Vector t = (SLT.GenSType t, SLT.TypeOneOf t [SLT.ECVec, SLT.ERVec])
type Matrix t = (SLT.GenSType t, SLT.TypeOneOf t [SLT.EMat, SLT.ESqMat])
type SameDimension t t' = SLI.Dimension t ~ SLI.Dimension t'
