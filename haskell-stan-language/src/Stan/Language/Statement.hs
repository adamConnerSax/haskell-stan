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
    SameTypeList,
    VecToSameTypedListF,
    SameTypedListToVecF, SameTypeList, GenSTypeList
    )
import Stan.Language.Indexing
    ( Sliced,
      N0,
    )
import Stan.Language.Operations ( BinaryResultT, SBinaryOp)
import Stan.Language.Functions
    ( Density,
      Function,
      FuncArg)


import Prelude hiding (Nat)
import Relude.Extra
import qualified Data.Vec.Lazy as Vec
import qualified Data.Type.Nat as DT

type family ForEachSlice (a :: EType) :: EType where
  ForEachSlice EInt = EInt -- required for looping over ranges. But Ick.
  ForEachSlice ECVec = EReal
  ForEachSlice ERVec = EReal
  ForEachSlice EMat = EReal
  ForEachSlice ESqMat = EReal
  ForEachSlice (EArray m t) = Sliced N0 (EArray m t)

data ForType t where
  SpecificNumbered :: SLE.UExpr EInt -> SLE.UExpr EInt -> ForType EInt
--  IndexedLoop :: SLE.IndexKey -> ForType EInt
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

data VarModifiers :: (EType -> Type) -> EType -> Type where
  Modifiers :: [VarModifier r t] -> VarModifiers r t
  NoModifiers :: VarModifiers r t

instance Semigroup (VarModifiers r t) where
  Modifiers a <> Modifiers b = Modifiers $ a <> b
  Modifiers a <> NoModifiers = Modifiers a
  NoModifiers <> Modifiers a = Modifiers a
  NoModifiers <> NoModifiers = NoModifiers

instance SLR.HFunctor VarModifiers where
  hfmap f = \case
    Modifiers ms -> Modifiers $ fmap (SLR.hfmap f) ms
    NoModifiers -> NoModifiers

instance SLR.HTraversable VarModifiers where
  htraverse nat = \case
    Modifiers ms -> Modifiers <$> traverse (SLR.htraverse nat) ms
    NoModifiers -> pure NoModifiers
  hmapM = SLR.htraverse

type VecToTListC f n = VecToSameTypedListF f EInt n
type TListToVecC f n = SameTypedListToVecF f EInt n

data DeclSpec :: (EType -> Type) -> EType -> Type  where
  ScalarSpec :: StanType t -> VarModifiers r (ScalarType t) -> DeclSpec r t
  VectorSpec :: StanType t -> r EInt -> VarModifiers r (ScalarType t) -> DeclSpec r t
  MatrixSpec :: StanType t -> r EInt -> r EInt -> VarModifiers r (ScalarType t) -> DeclSpec r t
  ArraySpec :: (forall f. VecToTListC f n, forall f.TListToVecC f n, GenSTypeList (SameTypeList EInt n), AllGenSTypes (SameTypeList EInt n))
    => DT.SNat (DT.S n) -> Vec.Vec (DT.S n) (r EInt) -> DeclSpec r t -> DeclSpec r (EArray (DT.S n) t)
  TupleSpec :: TypedList (DeclSpec r) ts -> DeclSpec r (ETuple ts)

instance SLR.HFunctor DeclSpec where
  hfmap f = \case
    ScalarSpec st vm -> ScalarSpec st (SLR.hfmap f vm)
    VectorSpec st l vm -> VectorSpec st (f l) (SLR.hfmap f vm)
    MatrixSpec st r c vm -> MatrixSpec st (f r) (f c) (SLR.hfmap f vm)
    ArraySpec n dv ds -> ArraySpec n (Vec.map f dv) (SLR.hfmap f ds)
    TupleSpec dss -> TupleSpec $ SLR.hfmap (SLR.hfmap f) dss

instance SLR.HTraversable DeclSpec where
  htraverse nat = \case
    ScalarSpec st vm -> ScalarSpec st <$> SLR.htraverse nat vm
    VectorSpec st l vm -> VectorSpec st <$> nat l <*> SLR.htraverse nat vm
    MatrixSpec st r c vm -> MatrixSpec st <$> nat r <*> nat c <*> SLR.htraverse nat vm
    ArraySpec n dv ds -> ArraySpec n <$> traverse nat dv <*> SLR.htraverse nat ds
    TupleSpec dss -> TupleSpec <$> SLR.htraverse (SLR.htraverse nat) dss
  hmapM = SLR.htraverse

data StmtBlock = FunctionsStmts
               | DataStmts
               | TDataStmts
               | ParametersStmts
               | TParametersStmts
               | ModelStmts
               | GeneratedQuantitiesStmts

data GroupType = Bracketed | UnBracketed | Scoping deriving stock (Show, Eq)


data StmtF :: (EType -> Type) -> Type -> Type where
  SDeclareF ::  Text -> DeclSpec r et -> StmtF r a
  SDeclAssignF :: Text -> DeclSpec r et -> r et -> StmtF r a
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
  SFunctionF :: Function rt args -> TypedList (FuncArg Text) args -> a -> StmtF r a
  SReturnF :: r t -> StmtF r a
  SCommentF :: Traversable f => f Text -> StmtF r a
  SProfileF :: Text -> a -> StmtF r a
  SPrintF :: TypedList r args -> StmtF r a
  SRejectF :: TypedList r args -> StmtF r a
  SBlockF :: StmtBlock -> a -> StmtF r a
  SGroupF :: Traversable f => GroupType -> f a -> StmtF r a
  SContextF :: (SLA.ASTCtxt -> SLA.ASTCtxt) -> StmtF r a

type UStmt = SLR.Fix (StmtF SLE.UExpr)
type LStmt = SLR.Fix (StmtF SLE.LExpr)

instance Semigroup UStmt where
  s1 <> s2 = SLR.Fix $ SGroupF UnBracketed [s1, s2]

instance Functor (StmtF f) where
  fmap f x = case x of
    SDeclareF txt ds -> SDeclareF txt ds
    SDeclAssignF txt ds rhse -> SDeclAssignF txt ds rhse
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
    SDeclareF txt ds -> pure $ SDeclareF txt ds
    SDeclAssignF txt ds fet -> pure $ SDeclAssignF txt ds fet
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

instance SLR.HFunctor StmtF where
  hfmap nat = \case
    SDeclareF txt ds -> SDeclareF txt (SLR.hfmap nat ds)
    SDeclAssignF txt ds rhe -> SDeclAssignF txt (SLR.hfmap nat ds) (nat rhe)
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
    SDeclareF txt ds -> SDeclareF txt <$> SLR.htraverse natM ds
    SDeclAssignF txt ds rhe -> SDeclAssignF txt <$> SLR.htraverse natM ds <*> natM rhe
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
