{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Stan.Language.ASTContext
  (
    ASTCtxt(..)
  , modifyVarCtxt
  , enterNewScope
  , leaveScope
  , indexes
  , sizes
  , varLookupMap
  , checkTypedVar
  , VarNameCheck(..)
  , FunctionCtxt(..)
  , modifyFunctionCtxt
  , addTypedVarToInnerScope
  , addTypedVarsInScope
  , emptyLookupCtxt
  )
  where

import qualified Stan.Language.Expression as SLE
import Stan.Language.Expressions (functionE)
import Stan.Language.Types
    ( EType(..),
      GenSType(..),
      SType,
      STypeList,
      sTypeName,
      TypedList,
      AllGenSTypes,
      sTypedFoldTypedList,
      oneTyped,
      FunctionName
    )
import Stan.Language.Functions
    (Function,
      simpleFunction )

import Data.Type.Nat (Nat(Z,S), SNatI)

import Prelude hiding (Nat)
--import Relude.Extra
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as Map
import qualified Data.Some as Some
import Stan.Language.Recursion (K(..))

type IndexArrayU = SLE.UExpr (EArray (S Z) EInt)
type IndexArrayL = SLE.LExpr (EArray (S Z) EInt)
type IndexSizeMap = Map SLE.IndexKey (SLE.LExpr EInt)
type IndexArrayMap = Map SLE.IndexKey IndexArrayL
type VarTypeMap = Map SLE.VarName (Some.Some SType)

data VarNameCheck = CheckPassed | NameMissing | WrongType Text

checkTypedVar :: SLE.VarName -> SType t -> VarTypeMap -> VarNameCheck
checkTypedVar vn st m = case Map.lookup vn m of
  Nothing -> NameMissing
  Just sst -> if Some.mkSome st == sst then CheckPassed else WrongType $ Some.withSome sst sTypeName

newtype VarLookupCtxt = VarLookupCtxt (NE.NonEmpty VarTypeMap) deriving newtype (Show)

emptyVarLookupCtxt :: VarLookupCtxt
emptyVarLookupCtxt = VarLookupCtxt $ mempty :| []

varLookupMap :: VarLookupCtxt -> VarTypeMap
varLookupMap (VarLookupCtxt vs) = fold vs

enterNewScope :: VarLookupCtxt -> VarLookupCtxt
enterNewScope (VarLookupCtxt (gs :| ls)) = VarLookupCtxt (gs :| mempty : ls)

leaveScope :: VarLookupCtxt -> VarLookupCtxt
leaveScope v@(VarLookupCtxt (_gs :| [])) = v
leaveScope (VarLookupCtxt (gs :| _ : os)) = VarLookupCtxt (gs :| os)

insertVarType :: SLE.VarName -> SType t -> VarTypeMap -> VarTypeMap
insertVarType vn st = Map.insert vn (Some.mkSome st)

addTypedVarToInnerScope :: SLE.VarName -> SType t -> VarLookupCtxt -> VarLookupCtxt
addTypedVarToInnerScope vn st (VarLookupCtxt (gs :| [])) = VarLookupCtxt $ insertVarType vn st gs :| []
addTypedVarToInnerScope vn st (VarLookupCtxt (gs :| is : os)) = VarLookupCtxt $ gs :| insertVarType vn st is : os

addTypedVarInScope :: SLE.VarName -> SType t -> VarLookupCtxt -> Maybe VarLookupCtxt
addTypedVarInScope vn st ctxt = mVLC where
  mExists = Map.lookup vn (varLookupMap ctxt)
  mVLC = case mExists of
    Nothing -> Just $ addTypedVarToInnerScope vn st ctxt
    Just _ -> Nothing

addTypedVarsInScope :: AllGenSTypes ts => TypedList (K SLE.VarName) ts -> VarLookupCtxt -> Maybe VarLookupCtxt
addTypedVarsInScope typedVarNames vlc = sTypedFoldTypedList f (Just vlc) typedVarNames
  where
    f (K vn) st mVlc = mVlc >>= addTypedVarInScope vn st

_addTypedVarsToInnerScope :: AllGenSTypes ts => TypedList (K SLE.VarName) ts -> VarLookupCtxt -> VarLookupCtxt
_addTypedVarsToInnerScope typedVarNames vlc = sTypedFoldTypedList f vlc typedVarNames
  where
    f (K vn) = addTypedVarToInnerScope vn


_array_num_elements :: (SNatI n, GenSType t) => Function EInt '[EArray n t]
_array_num_elements = simpleFunction "size" {- any chance this should be num_elements? --als was "inv"?? -}

_indexSize :: IndexArrayU -> SLE.UExpr EInt
_indexSize = functionE _array_num_elements . oneTyped

data IndexLookupCtxt = IndexLookupCtxt { sizes :: IndexSizeMap, indexes :: IndexArrayMap }

emptyIndexLookupCtxt :: IndexLookupCtxt
emptyIndexLookupCtxt = IndexLookupCtxt mempty mempty

--data FunctionNameStatus = FunctionName | FunctionNameAvailable
type FunctionTypeMap = Map FunctionName (Some.Some SType, Some.Some STypeList)

newtype FunctionCtxt = FunctionCtxt { functionNames :: FunctionTypeMap }

data ASTCtxt =
  ASTCtxt
  { varCtxt :: VarLookupCtxt
  , indexCtxt :: IndexLookupCtxt
  , functionCtxt :: FunctionCtxt
  }

emptyLookupCtxt :: ASTCtxt
emptyLookupCtxt = ASTCtxt emptyVarLookupCtxt emptyIndexLookupCtxt (FunctionCtxt Map.empty)

modifyVarCtxt :: (VarLookupCtxt -> VarLookupCtxt) -> ASTCtxt -> ASTCtxt
modifyVarCtxt f (ASTCtxt vlc ilc fc) = ASTCtxt (f vlc) ilc fc

_modifyIndexCtxt :: (IndexLookupCtxt -> IndexLookupCtxt) -> ASTCtxt -> ASTCtxt
_modifyIndexCtxt f (ASTCtxt vlc ilc fc) = ASTCtxt vlc (f ilc ) fc

modifyFunctionCtxt :: (FunctionCtxt -> FunctionCtxt) -> ASTCtxt -> ASTCtxt
modifyFunctionCtxt f (ASTCtxt vlc ilc fc) = ASTCtxt vlc ilc (f fc)
