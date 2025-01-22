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
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# LANGUAGE TypeOperators #-}

module Stan.Language.Evaluate
  (
    statementToCodeE
  , eStatementToCodeE
  )
where
--import qualified Stan.ModelBuilder.Expressions as SME
import Prelude hiding (Nat)

import qualified Stan.Language.ASTContext as SLA
import Stan.Language.Types ( EType(EInt, EArray)
                           , sTypeFromStanType
                           , SType(..), GenSType(..), GenSTypeList(..), AllGenSTypes, sTypeName, STypeList, FunctionName
                           )
import Stan.Language.Expression ( IndexKey, VarName, LExpr, LExprF (..), UExpr, UExprF(..), lNamedE )
import Stan.Language.Functions (Function(..), Density(..), TypedArgNames, funcArgName) --, withFunction, withDensity)
import Stan.Language.Statement
    ( LStmt,
      StmtF(..),
      ForEachSlice,
      UStmt,
      DeclSpec)
import Stan.Language.Statements (declType)
import Stan.Language.Recursion
    ( HFunctor(..),
      type (~>),
      HTraversable(..),
      NatM,
      K(..),
      IFix(..),
      iCata,
      iCataM,
      IAlgM, Fix(..), anaM, CoAlgM, hylo)
import Stan.Language.Format
    ( CodePP,
      iExprToCode,
      IExprCodeF(BareF),
      IExprCode,
      stmtToCodeE,
      exprToDocAlg,
      stmtToCodeAlg )

import Data.Type.Nat (Nat(S, Z))
import Data.Type.Equality ((:~:)(Refl), TestEquality(testEquality))

import qualified Data.Map.Strict as Map
import qualified Data.Some as Some

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

type LookupM = StateT SLA.ASTCtxt (Either Text)

lookupIndex :: IndexKey -> LookupM (LExpr (EArray (S Z) EInt))
lookupIndex k = do
  im <- gets (SLA.indexes . SLA.indexCtxt)
  case Map.lookup k im of
    Just e -> pure e
    Nothing -> lift $ Left $ "lookupIndex: \"" <> k <> "\" not found in index map."

lookupSize :: IndexKey -> LookupM (LExpr EInt)
lookupSize k = do
  sm <- gets (SLA.sizes . SLA.indexCtxt)
  case Map.lookup k sm of
    Just e -> pure e
    Nothing -> lift $ Left $ "lookupSize: \"" <> k <> "\" not found in size map."

lookupVar :: VarName -> SType t -> LookupM (LExpr t)
lookupVar vn st = do
  vtm <- gets $ SLA.varLookupMap . SLA.varCtxt
  case SLA.checkTypedVar vn st vtm of
    SLA.CheckPassed -> pure $ lNamedE vn st
    SLA.NameMissing -> do
      lift $ Left $ "variable name \"" <> vn <> "\" used but not declared."
    SLA.WrongType dt -> lift $ Left $ "variable name \"" <> vn <> "\" previously declared with type \"" <> dt <> " but used with type \"" <> sTypeName st <> "\""

newFunction :: Function t ts -> LookupM ()
newFunction = \case
  IdentityFunction -> lift $ Left "Evaluate: attempt to add new identity function!"
  Function @rt @ats fn -> do
    (SLA.FunctionCtxt fcm) <- gets SLA.functionCtxt
    case Map.lookup fn fcm of
      Nothing -> do
        let fcm' = Map.insert fn (Some.Some $ genSType @rt, Some.Some $ genSTypeList @ats) fcm
        modify $ SLA.modifyFunctionCtxt $ const $ SLA.FunctionCtxt fcm'
        pure ()
      Just _ -> lift $ Left $ "function name \"" <> fn <> "\" previously declared."


{-
For now, function lookup at call time is unimplemented because we'd need to pre-load all supported built-in functions.
Lookup functions exist below, should we choose to implement.
Typing is also tricky since many functions we support can be called at multiple types. We'd need an entry here for each.
-}

toLExprAlg :: IAlgM LookupM UExprF LExpr
toLExprAlg = \case
  UL le -> pure $ IFix le
  UIndex ik -> lookupIndex ik
  UIndexSize ik -> lookupSize ik
  UVarExpr name sType _le -> lookupVar name sType
  UFunction _f le -> pure $ IFix le
  UDensity _d le -> pure $ IFix le

doLookups :: NatM LookupM UExpr LExpr
doLookups = iCataM toLExprAlg

ucDeclare :: VarName -> DeclSpec UExpr t -> LookupM ()
ucDeclare varName ds =
  modify $ SLA.modifyVarCtxt $ SLA.addTypedVarToInnerScope varName $ sTypeFromStanType $ declType ds

ucAddIntCounterToLoopBodyScope :: VarName -> LookupM ()
ucAddIntCounterToLoopBodyScope vn = modify $ SLA.modifyVarCtxt $ SLA.addTypedVarToInnerScope vn SInt

ucAddTypedCounterToLoopBodyScope :: forall t r . GenSType (ForEachSlice t) => VarName -> r t -> LookupM ()
ucAddTypedCounterToLoopBodyScope vn _ce =
  modify $ SLA.modifyVarCtxt $ SLA.addTypedVarToInnerScope vn (genSType @(ForEachSlice t))

ucAddArgsToFunctionBodyScope :: AllGenSTypes args => TypedArgNames args -> LookupM ()
ucAddArgsToFunctionBodyScope fArgs = do
  vc <- gets SLA.varCtxt
  let newVCM = SLA.addTypedVarsInScope (hfmap (K . funcArgName) fArgs) $ SLA.enterNewScope vc
  case newVCM of
    Nothing -> lift $ Left "Error adding function arguments to function body scope"
    Just newVC -> modify (SLA.modifyVarCtxt $ const newVC)

updateContextA :: UStmt -> LookupM ()
updateContextA x = case unFix x of
  SDeclareF varName declSpec -> ucDeclare varName declSpec
  SDeclAssignF varName declSpec _ -> ucDeclare varName declSpec
  SForF loopCounter _ _ _ -> ucAddIntCounterToLoopBodyScope loopCounter
  SForEachF loopCounter ce _ -> ucAddTypedCounterToLoopBodyScope loopCounter ce
  SFunctionF f  typedArgs _ -> case f of
    Function _ -> do
      ucAddArgsToFunctionBodyScope typedArgs
      newFunction f
    IdentityFunction -> newFunction f
  SContextF f -> modify f
  _ -> pure ()

contextualLookup :: CoAlgM LookupM (StmtF LExpr) UStmt
contextualLookup x = do
  updateContextA x
  htraverse doLookups $ unFix x

doLookupsInCStatement :: UStmt -> LookupM LStmt
doLookupsInCStatement = anaM contextualLookup --contextualLookup'  --(\x -> htraverse doLookups (unFix x) >>= updateContext)

doLookupsInStatementE :: SLA.ASTCtxt -> UStmt -> Either Text LStmt
doLookupsInStatementE ctxt0 = flip evalStateT ctxt0 . doLookupsInCStatement

statementToCodeE :: SLA.ASTCtxt -> UStmt -> Either Text CodePP
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
  im <- gets (SLA.indexes . SLA.indexCtxt)
  case Map.lookup k im of
    Just e -> pure $ lExprToEExpr e
    Nothing -> pure $ IFix $ EE $ "#index: " <> k <> "#"

lookupSizeE :: IndexKey -> LookupM (EExpr EInt)
lookupSizeE k =  do
  im <- gets (SLA.sizes . SLA.indexCtxt)
  case Map.lookup k im of
    Just e -> pure $ lExprToEExpr e
    Nothing -> pure $ IFix $ EE $ "#size: " <> k <> "#"

lookupVarE :: VarName -> SType t -> LookupM (EExpr t)
lookupVarE vn st = do
  vtm <- gets $ SLA.varLookupMap . SLA.varCtxt
  case SLA.checkTypedVar vn st vtm of
    SLA.CheckPassed -> pure $ lExprToEExpr $ lNamedE vn st
    SLA.NameMissing -> do
      vc <- gets SLA.varCtxt
      pure $ IFix $ EE $ "#undeclared: " <> vn <> "# (varCtxt=" <> show vc  <> ")"
    SLA.WrongType _dt -> pure $ IFix $ EE $ "#badType \"" <> vn <> "#"

--type EStmt = Stmt EExpr
type EStmt = Fix (StmtF EExpr)

contextualLookupAE :: CoAlgM LookupM (StmtF EExpr) UStmt
contextualLookupAE x = do
  lsf <- htraverse doLookupsE $ unFix x
  updateContextA x
  pure lsf

doLookupsEInStatement :: UStmt -> LookupM EStmt
doLookupsEInStatement = anaM contextualLookupAE --(\x -> htraverse doLookupsE (RS.project x) >>= updateContext)

doLookupsEInStatementE :: SLA.ASTCtxt -> UStmt -> Either Text EStmt
doLookupsEInStatementE ctxt0 = flip evalStateT ctxt0 . doLookupsEInStatement

doLookupsE :: NatM LookupM UExpr EExpr
doLookupsE = iCataM $ \case
  UL le -> pure $ IFix $ EL le
  UIndex ik -> lookupIndexE ik
  UIndexSize ik -> lookupSizeE ik
  UVarExpr name sType _le -> lookupVarE name sType --pure $ IFix $ EL le
  UFunction _f le -> pure $ IFix $ EL le
  UDensity _d le -> pure $ IFix $ EL le

eExprToIExprCode :: EExpr ~> K IExprCode
eExprToIExprCode = iCata $ \case
  EL x -> exprToDocAlg x
  EE t -> K $ Fix $ BareF $ PP.pretty t

eExprToCode :: EExpr ~> K CodePP
eExprToCode = K . iExprToCode . unK . eExprToIExprCode

eStmtToCode :: EStmt -> Either Text CodePP
eStmtToCode = hylo stmtToCodeAlg (hfmap eExprToCode . unFix)

eStatementToCodeE :: SLA.ASTCtxt -> UStmt -> Either Text CodePP
eStatementToCodeE ctxt0 x = doLookupsEInStatementE ctxt0 x >>= eStmtToCode

-- currently unused because we'd need to preload all supported built-in functions
_calledFunction :: forall t ts . (GenSType t, GenSTypeList ts) => Function t ts -> LookupM ()
_calledFunction f = case f of
  IdentityFunction ->  pure ()
  Function fn -> do
    (SLA.FunctionCtxt fcm) <- gets SLA.functionCtxt
    case Map.lookup fn fcm of
      Nothing -> lift $ Left $ "Function \"" <> fn <> "\" called but no function by that name exists."
      Just (rtS, atsS) -> testFunctionTypes fn (genSType @t) (genSTypeList @ts) rtS atsS

_calledDensity :: forall t ts . (GenSType t, GenSTypeList ts) => Density t ts -> LookupM ()
_calledDensity (Density fn) = do
    (SLA.FunctionCtxt fcm) <- gets SLA.functionCtxt
    case Map.lookup fn fcm of
      Nothing -> lift $ Left $ "Density \"" <> fn <> "\" called but no function by that name exists."
      Just (gtS, atsS) -> testDensityTypes fn (genSType @t) (genSTypeList @ts) gtS atsS

testFunctionTypes :: FunctionName -> SType t -> STypeList ts -> Some.Some SType -> Some.Some STypeList -> LookupM ()
testFunctionTypes fn rt ats rtS atsS =
  Some.withSome rtS
  $ \rt' ->
      Some.withSome atsS
      $ \ats' -> case testEquality rt rt' of
                   Nothing -> lift $ Left $ "Function \"" <> fn <> "\" called and exists but return types don't match."
                   Just Refl -> case testEquality ats ats' of
                     Nothing -> lift $ Left $ "Function \"" <> fn <> "\" called and exists but argument types don't match."
                     Just Refl -> pure ()

testDensityTypes :: FunctionName -> SType t -> STypeList ts -> Some.Some SType -> Some.Some STypeList -> LookupM ()
testDensityTypes fn gt ats gtS atsS =
  Some.withSome gtS
  $ \gt' ->
      Some.withSome atsS
      $ \ats' -> case testEquality gt gt' of
                   Nothing -> lift $ Left $ "Density \"" <> fn <> "\" called and exists but given types don't match."
                   Just Refl -> case testEquality ats ats' of
                     Nothing -> lift $ Left $ "Density \"" <> fn <> "\" called and exists but argument types don't match."
                     Just Refl -> pure ()
