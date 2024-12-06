{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
--{-# LANGUAGE StandaloneDeriving #-}
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
    module Stan.Language.Functions
  )
  where

import Stan.Language.Types
import Stan.Language.TypedList


import Prelude hiding (Nat)
--import           Data.Kind (Type)


data Function :: EType -> [EType] -> Type  where
  Function :: Text
           -> SType t
           -> TypeList args
           -> Function t args
  IdentityFunction :: SType t -> Function t '[t]

--curryOneF :: Function t ts -> Function (t ::-> LastType ts) (AllButLast ts)
--curryOneF (Function n st tl tF) = Function n

-- Can't pattern match on the arg-mapping function in "where" or "let" since then args' would escape its scope.
-- But we can do this
withFunction :: (Text -> SType t -> TypeList args -> r)
                -> Function t args
                -> r
withFunction f (Function t st tl) = f t st tl
withFunction f (IdentityFunction st) = f "" st (st ::> TypeNil)

--simpleFunction :: (GenSType t, AllGenTypes args) => Text -> SType t -> TypeList args -> Function t args
--simpleFunction fn st args = Function fn st args id

simpleFunction :: (GenSType t, GenTypeList args) => Text -> Function t args
simpleFunction fn  = Function fn genSType genTypeList


functionArgTypes :: Function rt args -> TypeList args
functionArgTypes (Function _ _ al) = al
functionArgTypes (IdentityFunction t) = t ::> TypeNil

data Density :: EType -> [EType] -> Type where
  Density :: Text -- name
          -> SType t -- givens type
          -> TypeList args -- argument types
          -> Density t args

densityAsFunction :: Density gt ats -> Function EReal (gt ': ats)
densityAsFunction (Density n gt ats) = Function n SReal (gt ::> ats)

densityFunctionArgTypes :: Density gt args -> TypeList (gt ': args)
densityFunctionArgTypes (Density _ gt al) = gt ::> al

withDensity :: (Text -> SType t -> TypeList args -> r)
            -> Density t args
            -> r
withDensity f (Density dn st tl) = f dn st tl

simpleDensity :: (GenSType t, GenTypeList ts) => Text -> Density t ts
simpleDensity t  = Density t genSType genTypeList

-- const functor for holding arguments to functions
data FuncArg :: Type -> k -> Type where
  Arg :: a -> FuncArg a r
  DataArg :: a -> FuncArg a r

type TypedArgNames = TypedList (FuncArg Text)

funcArgName :: FuncArg Text a -> Text
funcArgName = \case
  Arg txt -> txt
  DataArg txt -> txt

mapFuncArg :: (a -> b) -> FuncArg a r -> FuncArg b r
mapFuncArg f = \case
  Arg a -> Arg $ f a
  DataArg a -> DataArg $ f a
