{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# LANGUAGE TypeOperators #-}

module Stan.Language.Evaluate
  (
    module Stan.Language.Evaluate
  )
where
--import qualified Stan.ModelBuilder.Expressions as SME
import Prelude hiding (Nat)

import Stan.Language.Types ( Nat(Z, S), EType(EInt, EArray), StanType, sTypeFromStanType, SType(..), GenSType(..), sTypeName)
import Stan.Language.TypedList (AllGenTypes)
import Stan.Language.Expressions ( IndexKey, VarName, LExpr, LExprF (..), UExpr, UExprF(..), lNamedE )
import Stan.Language.Functions (TypedArgNames, funcArgName)
import Stan.Language.Statements
    ( IndexLookupCtxt(sizes, indexes),
      LStmt,
      Stmt(..),
      StmtF(..),
      StmtBlock(..),
      ForEachSlice,
      UStmt, LookupCtxt (..), VarLookupCtxt, addTypedVarToInnerScope, addTypedVarsToInnerScope,
      addTypedVarsInScope,
      grouped, context,
      modifyVarCtxt, enterNewScope, dropScope, VarNameCheck (..), checkTypedVar, varLookupMap )
import Stan.Language.Recursion
    ( HFunctor(..),
      type (~>),
      HTraversable(..),
      NatM,
      K(..),
      IFix(..),
      iCata,
      anaM,
      iCataM,
      IAlgM, Fix, unFix)
import Stan.Language.Format
    ( CodePP,
      iExprToCode,
      IExprCode(Bare),
      stmtToCodeE,
      exprToDocAlg,
      stmtToCodeAlg )

import qualified Data.Functor.Foldable.Monadic as RS
import qualified Data.Functor.Foldable as RS

--import Control.Monad.State.Strict (withStateT)

import qualified Data.Map.Strict as Map

import qualified Prettyprinter as PP


{- Evaluation passes
1a. NatM LookupM UExpr LExpr (forall x. UExpr x -> LookupM LExpr x)
 - Do any lookups required to turn a UExpr into an LExpr
 - Since these are each fixed-points of HFunctors (parameterized by (EType -> Type)),
   this requires HFunctor recursion machinery.
1b. CStmt -> LookupM LStmt
 - CStmt has index expressions to look up within statement and context changes in the lookup environment.
 - LStmt has all things looked up.  This is now a tree of statements with expressions.

2a. (Runtime) error checks?
2b. Optimization (vectorization? CSE? Loop splitting or consolidating?)

3a. LExpr ~> FormattedText (expressions to Text but in HFunctor form)
3b. LStmt -> Stmt (FormattedText) (Statement tree with expressions to statement tree with Text for expressions.)
3c. FormattedText -> Text
3c. Stmt (FormattedText) -> Text (Produce code for statement tree)
-}

--type IndexKey = Text
data Context = Context {
                       }

type LookupM = StateT LookupCtxt (Either Text)
type ReaderM = ReaderT LookupCtxt (Either Text)

lookupIndex :: IndexKey -> LookupM (LExpr (EArray (S Z) EInt))
lookupIndex k = do
  im <- gets (indexes . indexCtxt)
  case Map.lookup k im of
    Just e -> pure e
    Nothing -> lift $ Left $ "lookupIndex: \"" <> k <> "\" not found in index map."

lookupSize :: IndexKey -> LookupM (LExpr EInt)
lookupSize k = do
  sm <- gets (sizes . indexCtxt)
  case Map.lookup k sm of
    Just e -> pure e
    Nothing -> lift $ Left $ "lookupSize: \"" <> k <> "\" not found in size map."

lookupVar :: VarName -> SType t -> LookupM (LExpr t)
lookupVar vn st = do
  vtm <- gets $ varLookupMap . varCtxt
  case checkTypedVar vn st vtm of
    CheckPassed -> pure $ lNamedE vn st
    NameMissing -> lift $ Left $ "variable name \"" <> vn <> "\" used but not declared."
    WrongType dt -> lift $ Left $ "variable name \"" <> vn <> "\" previously declared with type \"" <> dt <> " but used with type \"" <> sTypeName st <> "\""

toLExprAlg :: IAlgM LookupM UExprF LExpr
toLExprAlg = \case
  UL le -> pure $ IFix le
  UIndex ik -> lookupIndex ik
  UIndexSize ik -> lookupSize ik
  UVarExpr name sType _le -> lookupVar name sType

doLookups :: NatM LookupM UExpr LExpr
doLookups = iCataM toLExprAlg

ucDeclare :: VarName -> StanType t -> LookupM ()
ucDeclare varName stanType = modify $ modifyVarCtxt $ addTypedVarToInnerScope varName $ sTypeFromStanType stanType

ucAddIntCounterToLoopBodyScope :: VarName -> LookupM ()
ucAddIntCounterToLoopBodyScope vn = modify $ modifyVarCtxt $ addTypedVarToInnerScope vn SInt

ucAddTypedCounterToLoopBodyScope :: forall t r a . GenSType (ForEachSlice t) => VarName -> r t -> LookupM ()
ucAddTypedCounterToLoopBodyScope vn _ce = modify $ modifyVarCtxt $ addTypedVarToInnerScope vn (genSType @(ForEachSlice t))

ucAddArgsToFunctionBodyScope :: AllGenTypes args => TypedArgNames args -> LookupM ()
ucAddArgsToFunctionBodyScope fArgs = do
  vc <- gets varCtxt
  let newVCM = addTypedVarsInScope (hfmap (K . funcArgName) fArgs) $ enterNewScope vc
  case newVCM of
    Nothing -> lift $ Left "Error adding function arguments to function body scope"
    Just newVC -> modify (modifyVarCtxt $ const newVC)


contextualLookup :: UStmt -> LookupM (RS.Base LStmt UStmt)
contextualLookup x = do
  lsf <- htraverse doLookups (RS.project x)
  updateContextA x
  pure lsf

doLookupsInCStatement :: UStmt -> LookupM LStmt
doLookupsInCStatement = RS.anaM contextualLookup --(\x -> htraverse doLookups (RS.project x) >>= postContext)

--contextualLookupF :: (LookupCtxt -> UStmt) -> RS.Base LStmt (LookupCtxt -> UStmt)
--contextualLookupF f =
updateContextA :: UStmt -> LookupM ()--StmtF r a)
updateContextA = \case
  SDeclare varName stanType _ _ -> ucDeclare varName stanType
  SDeclAssign varName stanType _ _ _ -> ucDeclare varName stanType
  SFor loopCounter _ _ _ -> ucAddIntCounterToLoopBodyScope loopCounter
  SForEach loopCounter ce _ -> ucAddTypedCounterToLoopBodyScope loopCounter ce
  SFunction _ typedArgs _ _  -> ucAddArgsToFunctionBodyScope typedArgs
--  SBlockF stBlock body -> case stBlock of
--    ModelStmts -> modify (modifyVarCtxt enterNewScope)
--    _ -> pure ()
  SContext f -> modify f
  _ -> pure ()

ucAddTypedCounterToLoopBodyScopeF :: forall t r . GenSType (ForEachSlice t) => VarName -> r t -> LookupCtxt -> LookupCtxt
ucAddTypedCounterToLoopBodyScopeF vn _ce = modifyVarCtxt $ addTypedVarToInnerScope vn (genSType @(ForEachSlice t))

ucAddArgsToFunctionBodyScopeF :: AllGenTypes args => TypedArgNames args -> LookupCtxt -> LookupCtxt
ucAddArgsToFunctionBodyScopeF fArgs = modifyVarCtxt $ addTypedVarsToInnerScope (hfmap (K . funcArgName) fArgs) . enterNewScope


type UStmt' = Fix (StmtF UExpr)
type LStmt' = Fix (StmtF LExpr)
{-
doLookupsInCStatement' :: UStmt' -> LookupM LStmt'
doLookupsInCStatement' = anaM (\x -> htraverse doLookups (unFix x) >>= updateContext)
-}

doLookupsInStatementE :: LookupCtxt -> UStmt -> Either Text LStmt
doLookupsInStatementE ctxt0 = flip evalStateT ctxt0 . doLookupsInCStatement

statementToCodeE :: LookupCtxt -> UStmt -> Either Text CodePP
statementToCodeE ctxt0 x = doLookupsInStatementE ctxt0 x >>= stmtToCodeE

data EExprF :: (EType -> Type) -> EType -> Type where
  EL :: LExprF r t -> EExprF r t
  EE :: Text -> EExprF r t

instance HFunctor EExprF where
  hfmap nat = \case
    EL x -> EL $ hfmap nat x
    EE t -> EE t

instance HTraversable EExprF where
  htraverse natM = \case
    EL x -> EL <$> htraverse natM x
    EE t -> pure $ EE t
  hmapM = htraverse

type EExpr = IFix EExprF

lExprToEExpr :: LExpr t -> EExpr t
lExprToEExpr = iCata (IFix . EL)

lookupIndexE :: IndexKey -> LookupM (EExpr (EArray (S Z) EInt))
lookupIndexE k =  do
  im <- gets (indexes . indexCtxt)
  case Map.lookup k im of
    Just e -> pure $ lExprToEExpr e
    Nothing -> pure $ IFix $ EE $ "#index: " <> k <> "#"

lookupSizeE :: IndexKey -> LookupM (EExpr EInt)
lookupSizeE k =  do
  im <- gets (sizes . indexCtxt)
  case Map.lookup k im of
    Just e -> pure $ lExprToEExpr e
    Nothing -> pure $ IFix $ EE $ "#size: " <> k <> "#"

lookupVarE :: VarName -> SType t -> LookupM (EExpr t)
lookupVarE vn st = do
  vtm <- gets $ varLookupMap . varCtxt
  case checkTypedVar vn st vtm of
    CheckPassed -> pure $ lExprToEExpr $ lNamedE vn st
    NameMissing -> pure $ IFix $ EE $ "#undeclared: " <> vn <> "#"
    WrongType dt -> pure $ IFix $ EE $ "#badType \"" <> vn <> "#"

type EStmt = Stmt EExpr

contextualLookupAE :: UStmt -> LookupM (RS.Base EStmt UStmt)
contextualLookupAE x = do
  lsf <- htraverse doLookupsE (RS.project x)
  updateContextA x
  pure lsf


doLookupsEInStatement :: UStmt -> LookupM EStmt
doLookupsEInStatement = RS.anaM contextualLookupAE --(\x -> htraverse doLookupsE (RS.project x) >>= updateContext)

doLookupsEInStatementE :: LookupCtxt -> UStmt -> Either Text EStmt
doLookupsEInStatementE ctxt0 = flip evalStateT ctxt0 . doLookupsEInStatement

doLookupsE :: NatM LookupM UExpr EExpr
doLookupsE = iCataM $ \case
  UL le -> pure $ IFix $ EL le
  UIndex ik -> lookupIndexE ik
  UIndexSize ik -> lookupSizeE ik
  UVarExpr name sType _le -> lookupVarE name sType --pure $ IFix $ EL le

eExprToIExprCode :: EExpr ~> K IExprCode
eExprToIExprCode = iCata $ \case
  EL x -> exprToDocAlg x
  EE t -> K $ Bare $ PP.pretty t

eExprToCode :: EExpr ~> K CodePP
eExprToCode = K . iExprToCode . unK . eExprToIExprCode

eStmtToCode :: EStmt -> Either Text CodePP
eStmtToCode = RS.hylo stmtToCodeAlg (hfmap eExprToCode . RS.project)

eStatementToCodeE :: LookupCtxt -> UStmt -> Either Text CodePP
eStatementToCodeE ctxt0 x = doLookupsEInStatementE ctxt0 x >>= eStmtToCode

{-
contextualLookupE :: forall r a . UStmt -> LookupM (RS.Base EStmt UStmt)
contextualLookupE x = do
  (x', oc) <- addToLookupContext x
  lsf <- htraverse doLookupsE (RS.project x')
  put oc
  addToFollowingContext x'
  pure lsf


contextualLookupA :: forall r a .  RS.Base UStmt LStmt -> LookupM LStmt --LStmt -> LookupM (RS.Base LStmt LStmt)
contextualLookupA x = do
  (x', oc) <- addToLookupContextA x
  lsf <- htraverse doLookups x'
--  put oc
  addToFollowingContextA x'
  pure $ RS.embed lsf

modifyLC :: RS.Base UStmt a -> LookupCtxt -> LookupCtxt
modifyLC x = case x of
  SDeclareF varName stanType _ _ -> modifyVarCtxt  $ addTypedVarToInnerScope varName $ sTypeFromStanType stanType
  SDeclAssignF varName stanType _ _ _ ->  modifyVarCtxt $ addTypedVarToInnerScope varName $ sTypeFromStanType stanType
  SForF loopCounter _ _ _ -> modifyVarCtxt $ addTypedVarToInnerScope loopCounter SInt
  SForEachF loopCounter ce _ -> ucAddTypedCounterToLoopBodyScopeF loopCounter ce
  SFunctionF _ typedArgs _ _ -> ucAddArgsToFunctionBodyScopeF typedArgs
--  SScopedF _ -> modifyVarCtxt enterNewScope
  SBlockF stBlock _ -> case stBlock of
    ModelStmts -> modifyVarCtxt enterNewScope
    _ -> id
  SContextF f -> f

addToFollowingContext :: UStmt -> LookupM ()--StmtF r a)
addToFollowingContext = \case
  SDeclare varName stanType _ _ -> ucDeclare varName stanType
  SDeclAssign varName stanType _ _ _ -> ucDeclare varName stanType
  _ -> pure ()

addToFollowingContextA :: RS.Base UStmt LStmt -> LookupM ()--StmtF r a)
addToFollowingContextA = \case
  SDeclareF varName stanType _ _ -> ucDeclare varName stanType
  SDeclAssignF varName stanType _ _ _ -> ucDeclare varName stanType
  _ -> pure ()

addToLookupContext :: UStmt -> LookupM (UStmt, LookupCtxt)
addToLookupContext us = do
  oc <- get
  case us of
    SFor loopCounter _ _ _ -> ucAddIntCounterToLoopBodyScope loopCounter
    SForEach loopCounter ce _ -> ucAddTypedCounterToLoopBodyScope loopCounter ce
    SFunction _ typedArgs _ _  -> ucAddArgsToFunctionBodyScope typedArgs
--    SScoped _ -> modify (modifyVarCtxt enterNewScope)
    SBlock stBlock body -> case stBlock of
      ModelStmts -> modify (modifyVarCtxt enterNewScope)
      _ -> pure ()
    SContext f -> modify f
    _ -> pure ()
  pure (us, oc)

addToLookupContextA :: RS.Base UStmt LStmt -> LookupM (RS.Base UStmt LStmt, LookupCtxt)
addToLookupContextA us = do
  oc <- get
  case us of
    SForF loopCounter _ _ _ -> ucAddIntCounterToLoopBodyScope loopCounter
    SForEachF loopCounter ce _ -> ucAddTypedCounterToLoopBodyScope loopCounter ce
    SFunctionF _ typedArgs _ _  -> ucAddArgsToFunctionBodyScope typedArgs
--    SScopedF _ -> modify (modifyVarCtxt enterNewScope)
    SBlockF stBlock body -> case stBlock of
      ModelStmts -> modify (modifyVarCtxt enterNewScope)
      _ -> pure ()
    SContextF f -> modify f
    _ -> pure ()
  pure (us, oc)


-}
{-
g :: NatM LookupM UExpr EExpr --UExpr t -> LookupM (EExpr t)
g = \case
  UL x -> _

  iCataM $ \case
  UL x ->

--h :: NatM LookupM UExpr (EExprF UExpr)
--h = iCataM _
--  UL x -> pure $ IFix $ EL x


toEExprAlg :: IAlgM LookupM UExprF EExpr
toEExprAlg = \case
  UL x -> pure $ EL x
  UNamedIndex ik -> lookupUseE ik
  UNamedSize ik -> lookupSizeE ik

doLookupsE :: NatM LookupM UExpr EExpr
doLookupsE = iCataM toEExprAlg

--doLookupsEInCStatement :: UStmt -> LookupM EStmt
--doLookupsEInCStatement = RS.anaM (htraverse )
-}
