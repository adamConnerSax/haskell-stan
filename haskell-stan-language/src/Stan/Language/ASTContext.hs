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
    module Stan.Language.ASTContext
  )
  where

import Stan.Language.Expressions
    ( functionE,
      IndexKey,
      VarName,
      LExpr,
      UExpr )
import Stan.Language.Types
    ( EType(..),
      GenSType(..),
      SType,
      sTypeName,
      TypedList,
      AllGenSTypes,
      sTypedFoldTypedList,
      oneTyped
    )
import Stan.Language.Functions
    (Function,
      simpleFunction )

import Data.Type.Nat (Nat(Z,S), SNatI)

import Prelude hiding (Nat)
import Relude.Extra
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as Map
import qualified Data.Some as Some
import Stan.Language.Recursion (K(..))

type IndexArrayU = UExpr (EArray (S Z) EInt)
type IndexArrayL = LExpr (EArray (S Z) EInt)
type IndexSizeMap = Map IndexKey (LExpr EInt)
type IndexArrayMap = Map IndexKey IndexArrayL
type VarTypeMap = Map VarName (Some.Some SType)

data VarNameCheck = CheckPassed | NameMissing | WrongType Text

checkTypedVar :: VarName -> SType t -> VarTypeMap -> VarNameCheck
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

insertVarType :: VarName -> SType t -> VarTypeMap -> VarTypeMap
insertVarType vn st = Map.insert vn (Some.mkSome st)

addTypedVarToInnerScope :: VarName -> SType t -> VarLookupCtxt -> VarLookupCtxt
addTypedVarToInnerScope vn st (VarLookupCtxt (gs :| [])) = VarLookupCtxt $ insertVarType vn st gs :| []
addTypedVarToInnerScope vn st (VarLookupCtxt (gs :| is : os)) = VarLookupCtxt $ gs :| insertVarType vn st is : os

addTypedVarInScope :: VarName -> SType t -> VarLookupCtxt -> Maybe VarLookupCtxt
addTypedVarInScope vn st ctxt = mVLC where
  mExists = Map.lookup vn (varLookupMap ctxt)
  mVLC = case mExists of
    Nothing -> Just $ addTypedVarToInnerScope vn st ctxt
    Just _ -> Nothing

addTypedVarsInScope :: AllGenSTypes ts => TypedList (K VarName) ts -> VarLookupCtxt -> Maybe VarLookupCtxt
addTypedVarsInScope typedVarNames vlc = sTypedFoldTypedList f (Just vlc) typedVarNames
  where
    f (K vn) st mVlc = mVlc >>= addTypedVarInScope vn st

addTypedVarsToInnerScope :: AllGenSTypes ts => TypedList (K VarName) ts -> VarLookupCtxt -> VarLookupCtxt
addTypedVarsToInnerScope typedVarNames vlc = sTypedFoldTypedList f vlc typedVarNames
  where
    f (K vn) = addTypedVarToInnerScope vn


array_num_elements :: (SNatI n, GenSType t) => Function EInt '[EArray n t]
array_num_elements = simpleFunction "size" {- any chance this should be num_elements? --als was "inv"?? -}

indexSize :: IndexArrayU -> UExpr EInt
indexSize = functionE array_num_elements . oneTyped

data IndexLookupCtxt = IndexLookupCtxt { sizes :: IndexSizeMap, indexes :: IndexArrayMap }

emptyIndexLookupCtxt :: IndexLookupCtxt
emptyIndexLookupCtxt = IndexLookupCtxt mempty mempty

data ASTCtxt =
  ASTCtxt
  { varCtxt :: VarLookupCtxt
  , indexCtxt :: IndexLookupCtxt
  }

emptyLookupCtxt :: ASTCtxt
emptyLookupCtxt = ASTCtxt emptyVarLookupCtxt emptyIndexLookupCtxt

modifyVarCtxt :: (VarLookupCtxt -> VarLookupCtxt) -> ASTCtxt -> ASTCtxt
modifyVarCtxt f (ASTCtxt vlc ilc) = ASTCtxt (f vlc) ilc

modifyIndexCtxt :: (IndexLookupCtxt -> IndexLookupCtxt) -> ASTCtxt -> ASTCtxt
modifyIndexCtxt f (ASTCtxt vlc ilc) = ASTCtxt vlc $ f ilc
