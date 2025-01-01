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

module Stan.Language.CodeWriter
  (
    CodeWriter
  , MaybeCW
  , asCW
  , writeStmt
  , writeStmt_
  , writerL
  , writerL_
  , addStmt
  , (+%)
  , addStmts
  , declareW
  , declareNW
  , declareRHSW
  , declareRHSNW
  )
  where

import qualified Stan.Language.Statement as SLS
import qualified Stan.Language.Statements as SLSS
import Stan.Language.Expression (UExpr )
import Stan.Language.Expressions (namedE)
import Stan.Language.Types ( sTypeFromStanType)
import Control.Monad.Writer.Strict as W

import Prelude hiding (Nat)
--import Relude.Extra

newtype CodeWriter a = CodeWriter { _unCodeWriter :: W.Writer [SLS.UStmt] a } deriving newtype (Functor, Applicative, Monad, W.MonadWriter [SLS.UStmt])

data MaybeCW a = NoCW a | NeedsCW (CodeWriter a)

asCW :: MaybeCW a -> CodeWriter a
asCW (NoCW a) = pure a
asCW (NeedsCW cw) = cw

instance Functor MaybeCW where
  fmap f (NoCW a) = NoCW $ f a
  fmap f (NeedsCW cw) = NeedsCW $ fmap f cw

instance Applicative MaybeCW where
  pure = NoCW
  (NoCW f) <*> (NoCW a) = NoCW $ f a
  (NoCW f) <*> (NeedsCW cw) = NeedsCW $ fmap f cw
  (NeedsCW f) <*> (NoCW a) = NeedsCW $ f <*> (pure a)
  (NeedsCW f) <*> (NeedsCW cw) = NeedsCW $ f <*> cw

instance Monad MaybeCW where
  (NoCW a) >>= f = f a
  (NeedsCW cwa) >>= f = NeedsCW $ do
    a <- cwa
    case f a of
      NoCW b -> pure b
      NeedsCW cwb -> cwb

instance W.MonadWriter [SLS.UStmt] MaybeCW where
  tell w = NeedsCW $ W.tell w
  listen m = case m of
    NoCW a -> NoCW (a, [])
    NeedsCW cwa -> NeedsCW $ W.listen cwa
  pass m = case m of
    NoCW (a, _) -> NoCW a
    NeedsCW cw -> NeedsCW $ W.pass cw

writerL :: CodeWriter a -> ([SLS.UStmt], a)
writerL (CodeWriter w) = (stmts, a)
  where (a, stmts) = W.runWriter w

writeStmt :: CodeWriter a -> (SLS.UStmt, a)
writeStmt = first SLSS.grouped . writerL

writerL_ :: CodeWriter a -> [SLS.UStmt]
writerL_ = fst . writerL

writeStmt_ :: CodeWriter a -> SLS.UStmt
writeStmt_ = SLSS.grouped . writerL_

addStmt, (+%) :: SLS.UStmt -> CodeWriter ()
addStmt = W.tell . pure
(+%) = W.tell . pure

addStmts :: Traversable f => f SLS.UStmt -> CodeWriter ()
addStmts = traverse_ addStmt

declareW :: Text -> SLSS.DeclSpec t -> CodeWriter (UExpr t)
declareW t ds = do
  addStmt $ SLSS.declare t ds
  return $ namedE t (sTypeFromStanType $ SLSS.declType ds)

declareNW :: SLSS.NamedDeclSpec t -> CodeWriter (UExpr t)
declareNW nds = do
  addStmt $ SLSS.declareN nds
  return $ namedE (SLSS.declName nds) (sTypeFromStanType $ SLSS.declType $ SLSS.decl nds)

declareRHSW :: Text -> SLSS.DeclSpec t -> UExpr t -> CodeWriter (UExpr t)
declareRHSW t ds rhs = do
  addStmt $ SLSS.declareAndAssign t ds rhs
  return $ namedE t (sTypeFromStanType $ SLSS.declType ds)

declareRHSNW :: SLSS.NamedDeclSpec t -> UExpr t -> CodeWriter (UExpr t)
declareRHSNW nds rhs = do
  addStmt $ SLSS.declareAndAssignN nds rhs
  return $ namedE (SLSS.declName nds) (sTypeFromStanType $ SLSS.declType $ SLSS.decl nds)
