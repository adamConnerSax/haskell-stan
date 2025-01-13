{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeSynonymInstances #-}

{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}

module Stan.Language.Functions
  (
    Function(..)
  , simpleFunction
  , Density(..)
  , simpleDensity
  , densityAsFunction
  , FuncArg(..)
  , TypedArgNames
  , funcArgName
  , mapFuncArg
  )
  where

import Stan.Language.Types


import Prelude hiding (Nat)
--import           Data.Kind (Type)

data Function :: EType -> [EType] -> Type  where
  Function :: (GenSType t, AllGenSTypes ts, GenSTypeList ts) => FunctionName -> Function t ts
  IdentityFunction :: GenSType t => Function t '[t]

--curryOneF :: Function t ts -> Function (t ::-> LastType ts) (AllButLast ts)
--curryOneF (Function n st tl tF) = Function n
{-
-- Can't pattern match on the arg-mapping function in "where" or "let" since then args' would escape its scope.
-- But we can do this

withFunction :: (FunctionName -> SType t -> STypeList args -> r)
                -> Function t args
                -> r
withFunction f (Function t st tl) = f t st tl
withFunction f (IdentityFunction st) = f "" st (st :> TNil)
-}
--simpleFunction :: (GenSType t, AllGenTypes args) => Text -> SType t -> TypeList args -> Function t args
--simpleFunction fn st args = Function fn st args id

simpleFunction :: forall t ts . (GenSType t, AllGenSTypes ts, GenSTypeList ts) => Text -> Function t ts
simpleFunction = Function @t @ts


{-
functionArgTypes :: Function rt args -> STypeList args
functionArgTypes (Function _ _ al) = al
functionArgTypes (IdentityFunction t) = t :> TNil
-}

data Density :: EType -> [EType] -> Type where
  Density :: (GenSType t, AllGenSTypes ts, GenSTypeList ts) => FunctionName -> Density t ts

densityAsFunction :: forall gt ats . Density gt ats -> Function EReal (gt ': ats)
densityAsFunction (Density n) = Function @EReal @(gt ': ats) n

{-
densityFunctionArgTypes :: Density gt args -> STypeList (gt ': args)
densityFunctionArgTypes (Density _ gt al) = gt :> al


withDensity :: (FunctionName -> SType t -> STypeList args -> r)
            -> Density t args
            -> r
withDensity f (Density dn st tl) = f dn st tl
-}
simpleDensity :: forall t ts . (GenSType t, AllGenSTypes ts, GenSTypeList ts) => Text -> Density t ts
simpleDensity n = Density @t @ts n

-- const functor for holding arguments to functions
data FuncArg :: Type -> k -> Type where
  Arg :: a -> FuncArg a r
  DataArg :: a -> FuncArg a r

type TypedArgNames = TypedList (FuncArg VarName)

funcArgName :: FuncArg Text a -> VarName
funcArgName = \case
  Arg txt -> txt
  DataArg txt -> txt

mapFuncArg :: (a -> b) -> FuncArg a r -> FuncArg b r
mapFuncArg f = \case
  Arg a -> Arg $ f a
  DataArg a -> DataArg $ f a
