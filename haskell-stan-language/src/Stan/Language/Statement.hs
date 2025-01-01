{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Stan.Language.Statement
  (
    module Stan.Language.Statement
  )
  where

import qualified Stan.Language.Recursion as SLR
import qualified Stan.Language.ASTContext as SLA
import qualified Stan.Language.Expression as SLE
import Stan.Language.Types
  ( EType(..),
    GenSType(..),
    ScalarType,
    StanType(..),
    TypedList,
    AllGenSTypes,
    )
import Stan.Language.Indexing
    ( Sliced,
      N0,
      DeclIndexVecF
    )
import Stan.Language.Operations ( BinaryResultT, SBinaryOp)
import Stan.Language.Functions
    ( Density,
      Function,
      FuncArg)


import Prelude hiding (Nat)
import Relude.Extra
import qualified Data.Functor.Foldable as RS

type family ForEachSlice (a :: EType) :: EType where
  ForEachSlice EInt = EInt -- required for looping over ranges. But Ick.
  ForEachSlice ECVec = EReal
  ForEachSlice ERVec = EReal
  ForEachSlice EMat = EReal
  ForEachSlice ESqMat = EReal
  ForEachSlice (EArray m t) = Sliced N0 (EArray m t)

data ForType t where
  SpecificNumbered :: SLE.UExpr EInt -> SLE.UExpr EInt -> ForType EInt
  IndexedLoop :: SLE.IndexKey -> ForType EInt
  SpecificIn :: SLE.UExpr t -> ForType t
--  IndexedIn :: IndexKey -> UExpr t -> ForType t

data VarAndForType (t :: EType) where
  VarAndForType :: GenSType (ForEachSlice t) => Text -> ForType t -> VarAndForType t

data VarModifier :: (EType -> Type) -> EType -> Type where
  VarLower :: r t -> VarModifier r t
  VarUpper :: r t -> VarModifier r t
  VarOffset :: r t -> VarModifier r t
  VarMultiplier :: r t -> VarModifier r t

instance SLR.HFunctor VarModifier where
  hfmap f = \case
    VarLower x -> VarLower $ f x
    VarUpper x -> VarUpper $ f x
    VarOffset x -> VarOffset $ f x
    VarMultiplier x -> VarMultiplier $ f x

instance SLR.HTraversable VarModifier where
  htraverse nat = \case
    VarLower x -> VarLower <$> nat x
    VarUpper x -> VarUpper <$> nat x
    VarOffset x -> VarOffset <$> nat x
    VarMultiplier x -> VarMultiplier <$> nat x
  hmapM = SLR.htraverse

data StmtBlock = FunctionsStmts
               | DataStmts
               | TDataStmts
               | ParametersStmts
               | TParametersStmts
               | ModelStmts
               | GeneratedQuantitiesStmts

data GroupType = Bracketed | UnBracketed | Scoping deriving stock (Show, Eq)

-- Statements
data Stmt :: (EType -> Type) -> Type where
  SDeclare ::  Text -> StanType et -> DeclIndexVecF r et -> [VarModifier r (ScalarType et)] -> Stmt r
  SDeclAssign :: Text -> StanType et -> DeclIndexVecF r et -> [VarModifier r (ScalarType et)] -> r et -> Stmt r
  SAssign :: r t -> r t -> Stmt r
  SOpAssign :: (ta ~ BinaryResultT op ta tb) => SBinaryOp op -> r ta -> r tb -> Stmt r
  STarget :: r EReal -> Stmt r
  SSample :: r st -> Density st args -> TypedList r args -> Stmt r
  SFor :: Text -> r EInt -> r EInt -> Stmt r -> Stmt r
  SForEach :: GenSType (ForEachSlice t) => Text -> r t -> Stmt r -> Stmt r
  SIfElse :: NonEmpty (r EBool, Stmt r) -> Stmt r -> Stmt r -- [(condition, ifTrue)] -> ifAllFalse
  SWhile :: r EBool -> Stmt r -> Stmt r
  SBreak :: Stmt r
  SContinue :: Stmt r
  SFunction :: AllGenSTypes args => Function rt args -> TypedList (FuncArg Text) args -> Stmt r -> Stmt r
  SReturn :: r rt -> Stmt r
  SComment :: Traversable f => f Text -> Stmt r
  SProfile :: Text -> Stmt r -> Stmt r
  SPrint :: TypedList r args -> Stmt r
  SReject :: TypedList r args -> Stmt r
  SBlock :: StmtBlock -> Stmt r -> Stmt r
  SGroup :: Traversable f => GroupType -> f (Stmt r) -> Stmt r
  SContext :: (SLA.ASTCtxt -> SLA.ASTCtxt) -> Stmt r

data StmtF :: (EType -> Type) -> Type -> Type where
  SDeclareF ::  Text -> StanType et -> DeclIndexVecF r et -> [VarModifier r (ScalarType et)] -> StmtF r a
  SDeclAssignF :: Text -> StanType et -> DeclIndexVecF r et -> [VarModifier r (ScalarType et)] -> r et -> StmtF r a
  SAssignF :: r t -> r t -> StmtF r a
  SOpAssignF :: (ta ~ BinaryResultT op ta tb) => SBinaryOp op -> r ta -> r tb -> StmtF r a
  STargetF :: r EReal -> StmtF r a
  SSampleF :: r st -> Density st args -> TypedList r args -> StmtF r a
  SForF :: Text -> r EInt -> r EInt -> a -> StmtF r a
  SForEachF ::  GenSType (ForEachSlice t) => Text -> r t -> a -> StmtF r a
  SIfElseF :: NonEmpty (r EBool, a) -> a -> StmtF r a -- [(condition, ifTrue)] -> ifAllFalse
  SWhileF :: r EBool -> a -> StmtF r a
  SBreakF :: StmtF r a
  SContinueF :: StmtF r a
  SFunctionF :: AllGenSTypes args => Function rt args -> TypedList (FuncArg Text) args -> a -> StmtF r a
  SReturnF :: r t -> StmtF r a
  SCommentF :: Traversable f => f Text -> StmtF r a
  SProfileF :: Text -> a -> StmtF r a
  SPrintF :: TypedList r args -> StmtF r a
  SRejectF :: TypedList r args -> StmtF r a
  SBlockF :: StmtBlock -> a -> StmtF r a
  SGroupF :: Traversable f => GroupType -> f a -> StmtF r a
  SContextF :: (SLA.ASTCtxt -> SLA.ASTCtxt) -> StmtF r a

type instance RS.Base (Stmt f) = StmtF f

type LStmt = Stmt SLE.LExpr
type UStmt = Stmt SLE.UExpr

instance Functor (StmtF f) where
  fmap f x = case x of
    SDeclareF txt st divf vms -> SDeclareF txt st divf vms
    SDeclAssignF txt st divf vms rhse -> SDeclAssignF txt st divf vms rhse
    SAssignF ft ft' -> SAssignF ft ft'
    SOpAssignF op ft ft' -> SOpAssignF op ft ft'
    STargetF f' -> STargetF f'
    SSampleF f_st dis al -> SSampleF f_st dis al
    SForF ctr startE endE body -> SForF ctr startE endE (f body)
    SForEachF ctr fromE body -> SForEachF ctr fromE (f body)
    SIfElseF x1 sf -> SIfElseF (secondF f x1) (f sf)
    SWhileF cond sf -> SWhileF cond (f sf)
    SBreakF -> SBreakF
    SContinueF -> SContinueF
    SFunctionF func al sf -> SFunctionF func al (f sf)
    SReturnF re -> SReturnF re
    SCommentF t -> SCommentF t
    SProfileF t stmt -> SProfileF t (f stmt)
    SPrintF args -> SPrintF args
    SRejectF args -> SRejectF args
    SBlockF bl stmt -> SBlockF bl (f stmt)
    SGroupF s stmts -> SGroupF s  $ fmap f stmts
    SContextF cf -> SContextF cf

instance Foldable (StmtF f) where
  foldMap f = \case
    SDeclareF {} -> mempty
    SDeclAssignF {} -> mempty
    SAssignF {} -> mempty
    SOpAssignF {} -> mempty
    STargetF {} -> mempty
    SSampleF {} -> mempty
    SForF _ _ _ body -> f body
    SForEachF _ _ body -> f body
    SIfElseF ifConds sf -> foldMap (f . snd) ifConds <> f sf
    SWhileF _ body -> f body
    SBreakF -> mempty
    SContinueF -> mempty
    SFunctionF _ _ body -> f body
    SReturnF _ -> mempty
    SCommentF _ -> mempty
    SProfileF _ body -> f body
    SPrintF {} -> mempty
    SRejectF {} -> mempty
    SGroupF _ body -> foldMap f body
    SBlockF _ body -> f body
    SContextF _ -> mempty

instance Traversable (StmtF f) where
  traverse g = \case
    SDeclareF txt st divf vms -> pure $ SDeclareF txt st divf vms
    SDeclAssignF txt st divf vms fet -> pure $ SDeclAssignF txt st divf vms fet
    SAssignF ft ft' -> pure $ SAssignF ft ft'
    SOpAssignF op ft ft' -> pure $ SOpAssignF op ft ft'
    STargetF f -> pure $ STargetF f
    SSampleF f_st dis al -> pure $ SSampleF f_st dis al
    SForF txt f f' sfs -> SForF txt f f' <$> g sfs
    SForEachF txt ft sfs -> SForEachF txt ft <$> g sfs
    SIfElseF x0 sf -> SIfElseF <$> traverse (\(c, s) -> pure ((,) c) <*> g s) x0 <*> g sf
    SWhileF f body -> SWhileF f <$> g body
    SBreakF -> pure SBreakF
    SContinueF -> pure SContinueF
    SFunctionF func al sfs -> SFunctionF func al <$> g sfs
    SReturnF re -> pure $ SReturnF re
    SCommentF t -> pure $ SCommentF t
    SProfileF t stmts -> SProfileF t <$> g stmts
    SPrintF args -> pure $ SPrintF args
    SRejectF args -> pure $ SRejectF args
    SGroupF s stmts -> SGroupF s <$> traverse g stmts
    SBlockF bl stmt -> SBlockF bl <$> g stmt
    SContextF f  -> pure $ SContextF f

instance Functor (RS.Base (Stmt f)) => RS.Recursive (Stmt f) where
  project = \case
    SDeclare txt st divf vms -> SDeclareF txt st divf vms
    SDeclAssign txt st divf vms fet -> SDeclAssignF txt st divf vms fet
    SAssign ft ft' -> SAssignF ft ft'
    SOpAssign op ft ft' -> SOpAssignF op ft ft'
    STarget f -> STargetF f
    SSample f_st dis al -> SSampleF f_st dis al
    SFor txt f f' sts -> SForF txt f f' sts
    SForEach txt ft sts -> SForEachF txt ft sts
    SIfElse x0 st -> SIfElseF x0 st
    SWhile f sts -> SWhileF f sts
    SBreak -> SBreakF
    SContinue -> SContinueF
    SFunction func al sts -> SFunctionF func al sts
    SReturn re -> SReturnF re
    SComment t -> SCommentF t
    SProfile t body -> SProfileF t body
    SPrint args -> SPrintF args
    SReject args -> SRejectF args
    SGroup s sts -> SGroupF s sts
    SBlock bl sts -> SBlockF bl sts
    SContext mf -> SContextF mf

instance Functor (RS.Base (Stmt f)) => RS.Corecursive (Stmt f) where
  embed = \case
    SDeclareF txt st divf vms -> SDeclare txt st divf vms
    SDeclAssignF txt st divf vms fet -> SDeclAssign txt st divf vms fet
    SAssignF ft ft' -> SAssign ft ft'
    SOpAssignF op ft ft' -> SOpAssign op ft ft'
    STargetF f -> STarget f
    SSampleF f_st dis al -> SSample f_st dis al
    SForF txt f f' sts -> SFor txt f f' sts
    SForEachF txt ft sts -> SForEach txt ft sts
    SIfElseF x0 st -> SIfElse x0 st
    SWhileF f sts -> SWhile f sts
    SBreakF -> SBreak
    SContinueF -> SContinue
    SFunctionF func al sts -> SFunction func al sts
    SReturnF re -> SReturn re
    SCommentF t -> SComment t
    SProfileF t body -> SProfile t body
    SPrintF args -> SPrint args
    SRejectF args -> SReject args
    SGroupF s sts -> SGroup s sts
    SBlockF bl sts -> SBlock bl sts
    SContextF mf -> SContext mf

instance SLR.HFunctor StmtF where
  hfmap nat = \case
    SDeclareF txt st divf vms -> SDeclareF txt st (SLR.hfmap nat divf) (fmap (SLR.hfmap nat) vms)
    SDeclAssignF txt st divf vms rhe -> SDeclAssignF txt st (SLR.hfmap nat divf) (fmap (SLR.hfmap nat) vms) (nat rhe)
    SAssignF lhe rhe -> SAssignF (nat lhe) (nat rhe)
    SOpAssignF op lhe rhe -> SOpAssignF op (nat lhe) (nat rhe)
    STargetF rhe -> STargetF (nat rhe)
    SSampleF gst dis al -> SSampleF (nat gst) dis (SLR.hfmap nat al)
    SForF txt se ee body -> SForF txt (nat se) (nat ee) body
    SForEachF txt gt body -> SForEachF txt (nat gt) body
    SIfElseF x0 sf -> SIfElseF (firstF nat x0) sf
    SWhileF g body -> SWhileF (nat g) body
    SBreakF -> SBreakF
    SContinueF -> SContinueF
    SFunctionF func al body -> SFunctionF func al body
    SReturnF re -> SReturnF (nat re)
    SCommentF x -> SCommentF x
    SProfileF x body -> SProfileF x body
    SPrintF args -> SPrintF (SLR.hfmap nat args)
    SRejectF args -> SRejectF (SLR.hfmap nat args)
    SGroupF s body -> SGroupF s body
    SBlockF bl body -> SBlockF bl body
    SContextF mf -> SContextF mf

instance SLR.HTraversable StmtF where
  htraverse natM = \case
    SDeclareF txt st indexEs vms -> SDeclareF txt st <$> SLR.htraverse natM indexEs <*> traverse (SLR.htraverse natM) vms
    SDeclAssignF txt st indexEs vms rhe -> SDeclAssignF txt st <$> SLR.htraverse natM indexEs <*> traverse (SLR.htraverse natM) vms <*> natM rhe
    SAssignF lhe rhe -> SAssignF <$> natM lhe <*> natM rhe
    SOpAssignF op lhe rhe -> SOpAssignF op <$> natM lhe <*> natM rhe
    STargetF re -> STargetF <$> natM re
    SSampleF ste dist al -> SSampleF <$> natM ste <*> pure dist <*> SLR.htraverse natM al
    SForF txt se ee body -> SForF txt <$> natM se <*> natM ee <*> pure body
    SForEachF txt at' body -> SForEachF txt <$> natM at' <*> pure body
    SIfElseF x0 sf -> SIfElseF <$> traverse (\(c, s) -> (,) <$> natM c <*> pure s) x0 <*> pure sf
    SWhileF cond body -> SWhileF <$> natM cond <*> pure body
    SBreakF -> pure SBreakF
    SContinueF -> pure SContinueF
    SFunctionF func al body -> pure $ SFunctionF func al body
    SReturnF re -> SReturnF <$> natM re
    SCommentF x -> pure $ SCommentF x
    SProfileF x body -> pure $ SProfileF x body
    SPrintF args -> SPrintF <$> SLR.htraverse natM args
    SRejectF args -> SRejectF <$> SLR.htraverse natM args
    SGroupF s body -> pure $ SGroupF s body
    SBlockF bl body -> pure $ SBlockF bl body
    SContextF mf -> pure $ SContextF mf
  hmapM = SLR.htraverse
