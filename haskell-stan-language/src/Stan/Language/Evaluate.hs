{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
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

import Stan.Language.Types ( Nat(Z, S), EType(EInt, EArray) )
import Stan.Language.Expressions ( IndexKey, VarName, LExpr, LExprF, UExpr, UExprF(..) )
import Stan.Language.Statements
    ( IndexLookupCtxt(sizes, indexes),
      LStmt,
      Stmt,
      StmtF(SContextF),
      UStmt, LookupCtxt (..) )
import Stan.Language.Recursion
    ( HFunctor(..),
      type (~>),
      HTraversable(..),
      NatM,
      K(..),
      IFix(IFix,unIFix),
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

import Control.Monad.State.Strict (withStateT)

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

toLExprAlg :: IAlgM LookupM UExprF LExpr
toLExprAlg = \case
  UL le -> pure $ IFix le
  UIndex ik -> lookupIndex ik
  UIndexSize ik -> lookupSize ik
  UVarExpr _name _sType le -> pure $ IFix le

doLookups :: NatM LookupM UExpr LExpr
doLookups = iCataM toLExprAlg


updateContext :: StmtF r a -> LookupM (StmtF r a)
updateContext = \case
  SContextF mf body -> case mf of
    Nothing -> pure $ SContextF Nothing body
    Just f -> SContextF Nothing <$> withStateT f (pure body)
  x -> pure x

doLookupsInCStatement :: UStmt -> LookupM LStmt
doLookupsInCStatement = RS.anaM (\x -> htraverse doLookups (RS.project x) >>= updateContext)

type UStmt' = Fix (StmtF UExpr)
type LStmt' = Fix (StmtF LExpr)

doLookupsInCStatement' :: UStmt' -> LookupM LStmt'
doLookupsInCStatement' = anaM (\x -> htraverse doLookups (unFix x) >>= updateContext)


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

type EStmt = Stmt EExpr

doLookupsEInStatement :: UStmt -> LookupM EStmt
doLookupsEInStatement = RS.anaM (\x -> htraverse doLookupsE (RS.project x) >>= updateContext)

doLookupsEInStatementE :: LookupCtxt -> UStmt -> Either Text EStmt
doLookupsEInStatementE ctxt0 = flip evalStateT ctxt0 . doLookupsEInStatement

doLookupsE :: NatM LookupM UExpr EExpr
doLookupsE = iCataM $ \case
  UL le -> pure $ IFix $ EL le
  UIndex ik -> lookupIndexE ik
  UIndexSize ik -> lookupSizeE ik
  UVarExpr _name _sType le -> pure $ IFix $ EL le

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
