{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Stan.Builder.Build
  (
    module Stan.Builder.Build
  )
where

import qualified Stan.Builder.Core as SBC
import qualified Stan.Language.Types as SLT
import qualified Stan.Language.Expression as SLE
import qualified Stan.Language.Expressions as SLE
import qualified Stan.Language.Functions as SLF
import qualified Stan.Language.Program as SLP
import qualified Stan.Language.Statement as SLS -- was TE
import qualified Stan.Language.Statements as SLS -- was TE
import qualified Stan.Language.CodeWriter as SLC
import qualified Stan.Functions as SF

import Control.Monad (unless)
import qualified Data.Dependent.HashMap as DHash
import qualified Data.Set as Set

import Effectful ((:>), Eff)
import qualified Effectful.State.Static.Local as EffS

addToCurrentBlock :: SBC.StanCodeC es
                     => (SLP.StanBlock -> a -> Either Text (SLP.StanProgram -> SLP.StanProgram))
                     -> a
                     -> Eff es ()
addToCurrentBlock g s = do
  cb <- getBlock
  f <- SBC.buildEither $ g cb s
  modifyCode f

addToBlock :: SBC.StanCodeC es
              => (SLP.StanBlock -> a -> Either Text (SLP.StanProgram -> SLP.StanProgram))
              -> SLP.StanBlock
              -> a
              -> Eff es ()
addToBlock g ab s = do
  f <- SBC.buildEither $ g ab s
  modifyCode f

addStmtToCode :: SBC.StanCodeC es => SLS.UStmt -> Eff es ()
addStmtToCode = addToCurrentBlock SLP.addStmtToBlock

addStmtToBlock :: SBC.StanCodeC es => SLP.StanBlock -> SLS.UStmt -> Eff es ()
addStmtToBlock b = addToBlock SLP.addStmtToBlock b


addStmtsToCode :: (SBC.StanCodeC es , Traversable f)
                  => f SLS.UStmt -> Eff es ()
addStmtsToCode = addToCurrentBlock SLP.addStmtsToBlock

addStmtsToBlock :: (SBC.StanCodeC es , Traversable f)
                  => SLP.StanBlock -> f SLS.UStmt -> Eff es ()
addStmtsToBlock sb = addToBlock SLP.addStmtsToBlock sb


addStmtToCodeTop :: SBC.StanCodeC es =>  SLS.UStmt -> Eff es ()
addStmtToCodeTop = addToCurrentBlock SLP.addStmtToBlockTop

addStmtsToCodeTop :: (Traversable f, SBC.StanCodeC es) =>  f SLS.UStmt -> Eff es ()
addStmtsToCodeTop = addToCurrentBlock SLP.addStmtsToBlockTop

addFromCodeWriter :: SBC.StanCodeC es => SLC.CodeWriter a -> Eff es a
addFromCodeWriter cw = addStmtsToCode stmts >> return a
  where (stmts, a) = SLC.cwStmtList cw

addScopedFromCodeWriter :: SBC.StanCodeC es => SLC.CodeWriter a -> Eff es a
addScopedFromCodeWriter cw = addStmtsToCode [SLS.scoped $ SLS.grouped stmts] >> return a
  where (stmts, a) = SLC.cwStmtList cw

modifyCode' :: (SLP.StanProgram -> SLP.StanProgram) -> SBC.BuilderState md gq -> SBC.BuilderState md gq
modifyCode' f bs = let (SBC.StanCode currentBlock oldProg) = SBC.code bs in bs { SBC.code = SBC.StanCode currentBlock $ f oldProg }

modifyCode :: SBC.StanCodeC es => (SLP.StanProgram -> SLP.StanProgram) -> Eff es ()
modifyCode f = EffS.modify $ \(SBC.StanCode cb p) -> SBC.StanCode cb (f p)

modifyCodeE :: SBC.StanCodeC es => Either Text (SLP.StanProgram -> SLP.StanProgram) -> Eff es ()
modifyCodeE fE = SBC.buildEither fE >>= modifyCode

setBlock' :: SLP.StanBlock -> SBC.BuilderState md gq -> SBC.BuilderState md gq
setBlock' b bs = bs { SBC.code = (SBC.code bs) { SBC.curBlock = b} } -- lenses!

setBlock :: SBC.StanCodeC es => SLP.StanBlock -> Eff es ()
setBlock b = EffS.modify $ \(SBC.StanCode _ p) -> SBC.StanCode b p

getBlock :: SBC.StanCodeC es => Eff es SLP.StanBlock
getBlock = EffS.gets SBC.curBlock

inBlock :: SBC.StanCodeC es => SLP.StanBlock -> Eff es a -> Eff es a
inBlock b m = do
  oldBlock <- getBlock
  setBlock b
  a <- m
  setBlock oldBlock
  pure a

printExpr :: SBC.StanCodeC es => Text -> SLE.UExpr t -> Eff es ()
printExpr t e = addStmtToCode $ SLS.print (SLE.stringE ("\"" <> t <> "\"=") SLT.:> e SLT.:> SLT.TNil)

printTarget :: SBC.StanCodeC es => Text -> Eff es ()
printTarget _ = printExpr "target" SF.targetVal

modifyFunctionNames :: (Set Text -> Set Text) -> SBC.BuilderState md gq -> SBC.BuilderState md gq
modifyFunctionNames f bs = bs { SBC.hasFunctions = f (SBC.hasFunctions bs)}
--(BuilderState dv vbs mrb gqrb cj hf c) = BuilderState dv vbs mrb gqrb cj (f hf) c

addFunctionCodeOnce :: SBC.StanFunctionsC es => Text -> SLS.UStmt -> Eff es ()
addFunctionCodeOnce functionsName fCode = do
  fNames <- EffS.gets SBC.unFunctionNames
  Control.Monad.unless (functionsName `Set.member` fNames) $ do
    addStmtToBlock SLP.SBFunctions fCode
    EffS.modify $ SBC.FunctionNames . Set.insert functionsName . SBC.unFunctionNames

addFunctionOnce :: SBC.StanFunctionsC es
                => SLF.Function rt ats
                -> SLF.TypedArgNames ats
                -> (SLE.ExprList ats -> (SLS.UStmt, SLE.UExpr rt))
                -> Eff es (SLF.Function rt ats)
addFunctionOnce f@(SLF.Function fn) argNames fBF = do
  fNames <- EffS.gets SBC.unFunctionNames
  unless (fn `Set.member` fNames) $ do
    addStmtToBlock SLP.SBFunctions $ SLS.function f argNames fBF
    EffS.modify (SBC.FunctionNames . Set.insert fn . SBC.unFunctionNames)
  pure f

addFunctionOnce f@(SLF.IdentityFunction) _ _ = pure f


addDensityOnce :: (SLT.GenSType gt, SBC.StanFunctionsC es)
               => SLF.Density gt ats
               -> SLF.TypedArgNames (gt ': ats)
               -> (SLE.ExprList (gt ': ats) -> (SLS.UStmt, SLE.UExpr SLT.EReal))
               -> Eff es (SLF.Density gt ats)
addDensityOnce f@(SLF.Density fn) argNames fBF = do
  fsNames <- EffS.gets SBC.unFunctionNames
  unless (fn `Set.member` fsNames) $ do
    addStmtToBlock SLP.SBFunctions $  SLS.function (SLF.densityAsFunction f) argNames fBF
    EffS.modify (SBC.FunctionNames . Set.insert fn . SBC.unFunctionNames)
  pure f


getAndEmptyProgram :: SBC.StanCodeC es => Eff es SLP.StanProgram
getAndEmptyProgram = do
  (SBC.StanCode cb p) <- EffS.get
  EffS.put $ SBC.StanCode cb SLP.emptyStanProgram
  pure p

addProgramBelow :: SBC.StanCodeC es => SLP.StanProgram -> Eff es ()
addProgramBelow pBelow = do
  (SBC.StanCode cb pTop) <- EffS.get
  EffS.put $
    SBC.StanCode cb $ pTop <> pBelow

addCodeAbove :: SBC.StanCodeC es => Eff es () -> Eff es ()
addCodeAbove ma = do
  pBelow <- getAndEmptyProgram
  a <- ma
  addProgramBelow pBelow
  pure a

withRowInfo :: forall i d es y r . EffS.State (SBC.RowInfos i d) :> es
            => Eff es y
            -> (forall z . SBC.RowInfo z r -> Eff es y)
            -> SBC.RowTypeTag d r
            -> Eff es y
withRowInfo missing presentF rtt = EffS.get @(SBC.RowInfos i d) >>= maybe missing presentF . DHash.lookup rtt . SBC.unRowInfos
{-
varScopeBlock :: SLP.StanBlock -> SBC.StanBuilderM md gq ()
varScopeBlock sb = case sb of
  SLP.SBModel -> modify (modifyDeclaredVars $ changeVarScope SBC.ModelScope)
  SLP.SBGeneratedQuantities -> modify (modifyDeclaredVars $ changeVarScope SBC.GQScope)
  _ -> modify (modifyDeclaredVars $ changeVarScope SBC.GlobalScope)

inBlock :: SLP.StanBlock -> SBC.StanBuilderM md gq a -> SBC.StanBuilderM md gq a
inBlock b m = do
  oldBlock <- getBlock
  setBlock b
  varScopeBlock b
  x <- m
  setBlock oldBlock
  varScopeBlock oldBlock
  return x

isDeclared :: SLT.VarName -> SBC.StanBuilderM md gq Bool
isDeclared sn  = do
  sd <- SBC.declaredVars <$> get
  case varLookup sd sn of
    Left _ -> return False
    Right _ -> return True

isDeclaredAllScopes :: SLT.VarName -> SBC.StanBuilderM md gq Bool
isDeclaredAllScopes sn  = do
  sd <- SBC.declaredVars <$> get
  case varLookupAllScopes sd sn of
    Left _ -> return False
    Right _ -> return True


-- return True if variable is new, False if already declared
declare :: SLT.VarName -> SLT.StanType t -> SBC.StanBuilderM md gq Bool
declare sn st = do
--  let sv = SME.StanVar sn st
  sd <- SBC.declaredVars <$> get
  case varLookup sd sn of
    Left _ -> addVarInScope sn st >> return True
    Right et -> if et == SLT.eTypeFromStanType st
                then return False
                else SBC.stanBuildError $ "Attempt to re-declare \"" <> sn <> "\" with different type. Previous="
                     <> show et <> "; new=" <> show (SLT.eTypeFromStanType st)

changeVarScope :: SBC.VariableScope -> SBC.ScopedDeclarations -> SBC.ScopedDeclarations
changeVarScope vs sd = sd { SBC.currentScope = vs}

declarationsNE :: SBC.VariableScope -> SBC.ScopedDeclarations -> NonEmpty SBC.DeclarationMap
declarationsNE SBC.GlobalScope sd = SBC.globalScope sd
declarationsNE SBC.ModelScope sd = SBC.modelScope sd
declarationsNE SBC.GQScope sd = SBC.gqScope sd

setDeclarationsNE :: NonEmpty SBC.DeclarationMap -> SBC.VariableScope -> SBC.ScopedDeclarations -> SBC.ScopedDeclarations
setDeclarationsNE dmNE SBC.GlobalScope sd = sd { SBC.globalScope = dmNE}
setDeclarationsNE dmNE SBC.ModelScope sd = sd { SBC.modelScope = dmNE}
setDeclarationsNE dmNE SBC.GQScope sd = sd { SBC.gqScope = dmNE}

declarationsInScope :: SBC.ScopedDeclarations -> NonEmpty SBC.DeclarationMap
declarationsInScope sd = declarationsNE (SBC.currentScope sd) sd

addVarInScope :: SLT.VarName -> SLT.StanType t -> SBC.StanBuilderM md gq (SLE.UExpr t)
addVarInScope sn st = do
  let newSD sd = do
        _ <- alreadyDeclared sd sn st
        let curScope = SBC.currentScope sd
            dmNE = declarationsNE curScope sd
            SBC.DeclarationMap m = head dmNE
            dm' = SBC.DeclarationMap $ Map.insert sn (SLT.eTypeFromStanType st) m
            dmNE' = dm' :| tail dmNE
        return $ setDeclarationsNE dmNE' curScope sd
  bs <- get
  case modifyDeclaredVarsA newSD bs of
    Left errMsg -> SBC.stanBuildError errMsg
    Right newBS -> do
      put newBS
      pure $ SLE.namedE sn (SLT.sTypeFromStanType st)

varLookupInScope :: SBC.ScopedDeclarations -> SBC.VariableScope -> SLT.VarName -> Either Text SLT.EType
varLookupInScope sd sc sn = go $ toList dNE where
  dNE = declarationsNE sc sd
  go [] = Left $ "\"" <> sn <> "\" not declared/in scope (stan scope=" <> show sc <> ")."
  go ((SBC.DeclarationMap x) : xs) = case Map.lookup sn x of
    Nothing -> go xs
    Just et -> pure et

varLookup :: SBC.ScopedDeclarations -> SLT.VarName -> Either Text SLT.EType
varLookup sd = varLookupInScope sd (SBC.currentScope sd)

varLookupAllScopes :: SBC.ScopedDeclarations -> SLT.VarName -> Either Text SLT.EType
varLookupAllScopes sd sn =
  case varLookupInScope sd SBC.GlobalScope sn of
    Right x -> Right x
    Left _ -> case varLookupInScope sd SBC.ModelScope sn of
      Right x -> Right x
      Left _ -> varLookupInScope sd SBC.GQScope sn


alreadyDeclared :: SBC.ScopedDeclarations -> SLT.VarName -> SLT.StanType t  -> Either Text ()
alreadyDeclared sd sn st =
  case varLookup sd sn of
    Right et ->  if et == SLT.eTypeFromStanType st
                 then Left $ sn <> " already declared (with same type= " <> show et <> ")!"
                 else Left $ sn <> " (" <> show (SLT.eTypeFromStanType st)
                      <> ")already declared (with different type=" <> show et <> ")!"
    Left _ -> pure ()

alreadyDeclaredAllScopes :: SBC.ScopedDeclarations -> SLT.VarName -> SLT.StanType t -> Either Text ()
alreadyDeclaredAllScopes sd sn st =
  case varLookupAllScopes sd sn of
    Right et ->  if et == SLT.eTypeFromStanType st
                 then Left $ sn <> " already declared (with same type= " <> show et <> ")!"
                 else Left $ sn <> " (" <> show (SLT.eTypeFromStanType st)
                      <> ")already declared (with different type=" <> show et <> ")!"
    Left _ -> pure ()
-}


{-
withRowInfo' :: forall md gq es y r . EffS.State (SBC.RowBuilders md gq) :> es
            => Eff es y
            -> (forall x . SBC.RowInfo x r -> Eff es y)
            -> SBC.RowTypeTag r
            -> Eff es y
withRowInfo' missing presentF rtt = do
  case SBC.inputDataType rtt of
    SBC.ModelData -> EffS.gets @(SBC.RowBuilders md gq) SBC.modelRBs >>= maybe missing presentF . DHash.lookup rtt
    SBC.GQData -> EffS.gets @(SBC.RowBuilders md gq) SBC.gqRBs >>= maybe missing presentF . DHash.lookup rtt
-}
{-
withRowInfo :: SBC.StanBuilderM md gq y -> (forall x . SBC.RowInfo x r -> SBC.StanBuilderM md gq y) -> SBC.RowTypeTag r -> SBC.StanBuilderM md gq y
withRowInfo missing presentF rtt = do
  case SBC.inputDataType rtt of
    SBC.ModelData -> do
      rowInfos <- SBC.modelRowBuilders <$> get
      maybe missing presentF $ DHash.lookup rtt rowInfos
    SBC.GQData -> do
      rowInfos <- SBC.gqRowBuilders <$> get
      maybe missing presentF $ DHash.lookup rtt rowInfos


getDataSetBindingsEff :: SBC.StateAndFailEff (SBC.RowBuilders md gq) es => SBC.RowTypeTag r -> Eff es SLA.IndexArrayMap
getDataSetBindingsEff rtt = withRowInfoEff err (pure . SBC.expressionBindings) rtt where
  idt = SBC.inputDataType rtt
  err = SBC.effBuildError $ "getDataSetbindings: row-info=" <> SBC.dataSetName rtt <> " not found in " <> show idt

getDataSetBindings :: SBC.RowTypeTag r -> SBC.StanBuilderM md gq SLA.IndexArrayMap
getDataSetBindings rtt = withRowInfo err (return .  SBC.expressionBindings) rtt where
  idt = SBC.inputDataType rtt
  err = SBC.stanBuildError $ "getDataSetbindings: row-info=" <> SBC.dataSetName rtt <> " not found in " <> show idt

setDataSetForBindings :: SBC.RowTypeTag r -> SBC.StanBuilderM md gq ()
setDataSetForBindings rtt = do
  newUseBindings <- getDataSetBindings rtt
  modify $ modifyIndexBindings (\lc -> lc { SLA.indexes = newUseBindings })

useDataSetForBindings :: SBC.RowTypeTag r -> SBC.StanBuilderM md gq a -> SBC.StanBuilderM md gq a
useDataSetForBindings rtt x = getDataSetBindings rtt >>= flip withUseBindings x

-- add anything not already present
addDataSetBindings :: SBC.RowTypeTag r -> SBC.StanBuilderM md gq a -> SBC.StanBuilderM md gq a
addDataSetBindings rtt x = getDataSetBindings rtt >>= flip extendUseBindings x

modifyDeclaredVars :: (SBC.ScopedDeclarations -> SBC.ScopedDeclarations) -> SBC.BuilderState md gq -> SBC.BuilderState md gq
modifyDeclaredVars f bs = bs {SBC.declaredVars = f (SBC.declaredVars bs)}
--(BuilderState dv vbs mrb gqrb cj hf c) = BuilderState (f dv) vbs mrb gqrb cj hf c

modifyDeclaredVarsA :: Applicative t
                    => (SBC.ScopedDeclarations -> t SBC.ScopedDeclarations)
                    -> SBC.BuilderState md gq
                    -> t (SBC.BuilderState md gq)
modifyDeclaredVarsA f bs = (\x -> bs { SBC.declaredVars = x}) <$> f (SBC.declaredVars bs)
-- (BuilderState dv vbs mrb gqrb cj hf c) = (\x -> BuilderState x vbs mrb gqrb cj hf c) <$> f dv

modifyIndexBindings :: (SLA.IndexLookupCtxt -> SLA.IndexLookupCtxt)
                    -> SBC.BuilderState md gq
                    -> SBC.BuilderState md gq
modifyIndexBindings f bs = bs {SBC.indexBindings = f (SBC.indexBindings bs)}
--(BuilderState dv vbs mrb gqrb cj hf c) = BuilderState dv (f vbs) mrb gqrb cj hf c

modifyIndexBindingsA :: Applicative t
                     => (SLA.IndexLookupCtxt -> t SLA.IndexLookupCtxt)
                     -> SBC.BuilderState md gq
                     -> t (SBC.BuilderState md gq)
modifyIndexBindingsA f bs = (\x -> bs {SBC.indexBindings = x}) <$> f (SBC.indexBindings bs)
--(BuilderState dv vbs mrb gqrb cj hf c) = (\x -> BuilderState dv x mrb gqrb cj hf c) <$> f vbs

withUseBindings :: SLA.IndexArrayMap -> SBC.StanBuilderM md gq a -> SBC.StanBuilderM md gq a
withUseBindings ubs m = do
  oldBindings <- SBC.indexBindings <$> get
  modify $ modifyIndexBindings (\lc -> lc {SLA.indexes = ubs})
  a <- m
  modify $ modifyIndexBindings $ const oldBindings
  return a

extendUseBindings :: SLA.IndexArrayMap -> SBC.StanBuilderM md gq a -> SBC.StanBuilderM md gq a
extendUseBindings ubs' m = do
  oldBindings <- SBC.indexBindings <$> get
  modify $ modifyIndexBindings (\lc -> lc {SLA.indexes = Map.union ubs' (SLA.indexes lc)})
  a <- m
  modify $ modifyIndexBindings $ const oldBindings
  return a

withDeclBindings :: SLA.IndexSizeMap -> SBC.StanBuilderM md gq a -> SBC.StanBuilderM md gq a
withDeclBindings dbs m = do
  oldBindings <- SBC.indexBindings <$> get
  modify $ modifyIndexBindings (\lc -> lc {SLA.sizes = dbs})
  a <- m
  modify $ modifyIndexBindings $ const oldBindings
  return a

extendDeclBindings :: SLA.IndexSizeMap -> SBC.StanBuilderM md gq a -> SBC.StanBuilderM md gq a
extendDeclBindings dbs' m = do
  oldBindings <- SBC.indexBindings <$> get
  modify $ modifyIndexBindings (\lc -> lc {SLA.sizes = Map.union dbs' (SLA.sizes lc)})
  a <- m
  modify $ modifyIndexBindings $ const oldBindings
  return a

addScopedDeclBindings :: SLA.IndexSizeMap -> SBC.StanBuilderM env d a -> SBC.StanBuilderM env d a
addScopedDeclBindings dbs' m = do
  oldBindings <- SBC.indexBindings <$> get
  modify $ modifyIndexBindings (\lc -> lc {SLA.sizes = Map.union dbs' (SLA.sizes lc)})
  a <- m
  modify $ modifyIndexBindings $ const oldBindings
  return a
-}
{-
modifyModelRowInfosA :: Applicative t
                   => (SBC.RowInfos md -> t (SBC.RowInfos md))
                   -> SBC.BuilderState md gq
                   -> t (SBC.BuilderState md gq)
modifyModelRowInfosA f bs = (\x -> bs {SBC.modelRowBuilders = x}) <$> f (SBC.modelRowBuilders bs)
--(BuilderState dv vbs mrb gqrb cj hf c) = (\x -> BuilderState dv vbs x gqrb cj hf c) <$> f mrb

modifyGQRowInfosA :: Applicative t
                   => (SBC.RowInfos gq -> t (SBC.RowInfos gq))
                   -> SBC.BuilderState md gq
                   -> t (SBC.BuilderState md gq)
modifyGQRowInfosA f bs = (\x -> bs {SBC.gqRowBuilders = x}) <$> f (SBC.gqRowBuilders bs)
--(BuilderState dv vbs mrb gqrb cj hf c) = (\x -> BuilderState dv vbs mrb x cj hf c) <$> f gqrb
-}
{-
modifyConstJson :: SBC.InputDataType -> (SBC.JSONSeriesFold () -> SBC.JSONSeriesFold ()) -> SBC.BuilderState md gq -> SBC.BuilderState md gq
modifyConstJson idt f bs = case idt of
  SBC.ModelData -> bs { SBC.constModelJSON = f (SBC.constModelJSON bs)}
  SBC.GQData -> bs { SBC.constGQJSON = f (SBC.constGQJSON bs)}
--(BuilderState dvs ibs mrbs gqrbs cj hfs c) = BuilderState dvs ibs mrbs gqrbs (f cj) hfs c

addConstJson :: SBC.InputDataType -> SBC.JSONSeriesFold () -> SBC.BuilderState md gq -> SBC.BuilderState md gq
addConstJson idt jf = modifyConstJson idt (<> jf)
-}
