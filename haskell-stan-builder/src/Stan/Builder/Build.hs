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

import qualified Stan.Builder.CoreTypes as SBC
import qualified Stan.Language.Types as SLT
import qualified Stan.Language.Expressions as SLE
import qualified Stan.Language.Functions as SLF
import qualified Stan.Language.Program as SLP
--import qualified Stan.Language.Format as SLF
import qualified Stan.Language.Statements as SLS -- was TE
--import qualified Stan.Builder.ParameterTypes as SBPT
import qualified Control.Monad.Writer.Strict as W
import qualified Data.Dependent.HashMap as DHash
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
--import qualified Data.List.NonEmpty as NE

addStmtToCode :: SLS.UStmt -> SBC.StanBuilderM md gq ()
addStmtToCode stmt = do
  cb <- getBlock
  f <- SBC.stanBuildEither $ SLP.addStmtToBlock cb stmt
  modifyCode f

addStmtsToCode :: Traversable f => f SLS.UStmt -> SBC.StanBuilderM md gq ()
addStmtsToCode stmts = do
  cb <- getBlock
  f <- SBC.stanBuildEither $ SLP.addStmtsToBlock cb stmts
  modifyCode f

addStmtToCodeTop :: SLS.UStmt -> SBC.StanBuilderM md gq ()
addStmtToCodeTop stmt = do
  cb <- getBlock
  f <- SBC.stanBuildEither $ SLP.addStmtToBlockTop cb stmt
  modifyCode f

addStmtsToCodeTop :: Traversable f => f SLS.UStmt -> SBC.StanBuilderM md gq ()
addStmtsToCodeTop stmts = do
  cb <- getBlock
  f <- SBC.stanBuildEither $ SLP.addStmtsToBlockTop cb stmts
  modifyCode f

addFromCodeWriter :: SLS.CodeWriter a -> SBC.StanBuilderM md gq a
addFromCodeWriter (SLS.CodeWriter cw) = addStmtsToCode stmts >> return a
  where (a, stmts) = W.runWriter cw

addScopedFromCodeWriter :: SLS.CodeWriter a -> SBC.StanBuilderM md gq a
addScopedFromCodeWriter (SLS.CodeWriter cw) = addStmtsToCode [SLS.scoped stmts] >> return a
  where (a, stmts) = W.runWriter cw

modifyCode' :: (SLP.StanProgram -> SLP.StanProgram) -> SBC.BuilderState md gq -> SBC.BuilderState md gq
modifyCode' f bs = let (SBC.StanCode currentBlock oldProg) = SBC.code bs in bs { SBC.code = SBC.StanCode currentBlock $ f oldProg }

modifyCode :: (SLP.StanProgram -> SLP.StanProgram) -> SBC.StanBuilderM md gq ()
modifyCode f = modify $ modifyCode' f

modifyCodeE :: Either Text (SLP.StanProgram -> SLP.StanProgram) -> SBC.StanBuilderM md gq ()
modifyCodeE fE = SBC.stanBuildEither fE >>= modifyCode

setBlock' :: SLP.StanBlock -> SBC.BuilderState md gq -> SBC.BuilderState md gq
setBlock' b bs = bs { SBC.code = (SBC.code bs) { SBC.curBlock = b} } -- lenses!

setBlock :: SLP.StanBlock -> SBC.StanBuilderM md gq ()
setBlock = modify . setBlock'

getBlock :: SBC.StanBuilderM md gq SLP.StanBlock
getBlock = gets (SBC.curBlock . SBC.code)

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

isDeclared :: SLS.StanName -> SBC.StanBuilderM md gq Bool
isDeclared sn  = do
  sd <- SBC.declaredVars <$> get
  case varLookup sd sn of
    Left _ -> return False
    Right _ -> return True

isDeclaredAllScopes :: SLS.StanName -> SBC.StanBuilderM md gq Bool
isDeclaredAllScopes sn  = do
  sd <- SBC.declaredVars <$> get
  case varLookupAllScopes sd sn of
    Left _ -> return False
    Right _ -> return True


-- return True if variable is new, False if already declared
declare :: SLS.StanName -> SLT.StanType t -> SBC.StanBuilderM md gq Bool
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

addVarInScope :: SLS.StanName -> SLT.StanType t -> SBC.StanBuilderM md gq (SLS.UExpr t)
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

varLookupInScope :: SBC.ScopedDeclarations -> SBC.VariableScope -> SLS.StanName -> Either Text SLT.EType
varLookupInScope sd sc sn = go $ toList dNE where
  dNE = declarationsNE sc sd
  go [] = Left $ "\"" <> sn <> "\" not declared/in scope (stan scope=" <> show sc <> ")."
  go ((SBC.DeclarationMap x) : xs) = case Map.lookup sn x of
    Nothing -> go xs
    Just et -> pure et

varLookup :: SBC.ScopedDeclarations -> SLS.StanName -> Either Text SLT.EType
varLookup sd = varLookupInScope sd (SBC.currentScope sd)

varLookupAllScopes :: SBC.ScopedDeclarations -> SLS.StanName -> Either Text SLT.EType
varLookupAllScopes sd sn =
  case varLookupInScope sd SBC.GlobalScope sn of
    Right x -> Right x
    Left _ -> case varLookupInScope sd SBC.ModelScope sn of
      Right x -> Right x
      Left _ -> varLookupInScope sd SBC.GQScope sn


alreadyDeclared :: SBC.ScopedDeclarations -> SLS.StanName -> SLT.StanType t  -> Either Text ()
alreadyDeclared sd sn st =
  case varLookup sd sn of
    Right et ->  if et == SLT.eTypeFromStanType st
                 then Left $ sn <> " already declared (with same type= " <> show et <> ")!"
                 else Left $ sn <> " (" <> show (SLT.eTypeFromStanType st)
                      <> ")already declared (with different type=" <> show et <> ")!"
    Left _ -> pure ()

alreadyDeclaredAllScopes :: SBC.ScopedDeclarations -> SLS.StanName -> SLT.StanType t -> Either Text ()
alreadyDeclaredAllScopes sd sn st =
  case varLookupAllScopes sd sn of
    Right et ->  if et == SLT.eTypeFromStanType st
                 then Left $ sn <> " already declared (with same type= " <> show et <> ")!"
                 else Left $ sn <> " (" <> show (SLT.eTypeFromStanType st)
                      <> ")already declared (with different type=" <> show et <> ")!"
    Left _ -> pure ()

withRowInfo :: SBC.StanBuilderM md gq y -> (forall x . SBC.RowInfo x r -> SBC.StanBuilderM md gq y) -> SBC.RowTypeTag r -> SBC.StanBuilderM md gq y
withRowInfo missing presentF rtt =
  case SBC.inputDataType rtt of
    SBC.ModelData -> do
      rowInfos <- SBC.modelRowBuilders <$> get
      maybe missing presentF $ DHash.lookup rtt rowInfos
    SBC.GQData -> do
      rowInfos <- SBC.gqRowBuilders <$> get
      maybe missing presentF $ DHash.lookup rtt rowInfos

getDataSetBindings :: SBC.RowTypeTag r -> SBC.StanBuilderM md gq SLS.IndexArrayMap
getDataSetBindings rtt = withRowInfo err (return .  SBC.expressionBindings) rtt where
  idt = SBC.inputDataType rtt
  err = SBC.stanBuildError $ "getDataSetbindings: row-info=" <> SBC.dataSetName rtt <> " not found in " <> show idt

setDataSetForBindings :: SBC.RowTypeTag r -> SBC.StanBuilderM md gq ()
setDataSetForBindings rtt = do
  newUseBindings <- getDataSetBindings rtt
  modify $ modifyIndexBindings (\lc -> lc { SLS.indexes = newUseBindings })

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

modifyIndexBindings :: (SLS.IndexLookupCtxt -> SLS.IndexLookupCtxt)
                    -> SBC.BuilderState md gq
                    -> SBC.BuilderState md gq
modifyIndexBindings f bs = bs {SBC.indexBindings = f (SBC.indexBindings bs)}
--(BuilderState dv vbs mrb gqrb cj hf c) = BuilderState dv (f vbs) mrb gqrb cj hf c

modifyIndexBindingsA :: Applicative t
                     => (SLS.IndexLookupCtxt -> t SLS.IndexLookupCtxt)
                     -> SBC.BuilderState md gq
                     -> t (SBC.BuilderState md gq)
modifyIndexBindingsA f bs = (\x -> bs {SBC.indexBindings = x}) <$> f (SBC.indexBindings bs)
--(BuilderState dv vbs mrb gqrb cj hf c) = (\x -> BuilderState dv x mrb gqrb cj hf c) <$> f vbs

withUseBindings :: SLS.IndexArrayMap -> SBC.StanBuilderM md gq a -> SBC.StanBuilderM md gq a
withUseBindings ubs m = do
  oldBindings <- SBC.indexBindings <$> get
  modify $ modifyIndexBindings (\lc -> lc {SLS.indexes = ubs})
  a <- m
  modify $ modifyIndexBindings $ const oldBindings
  return a

extendUseBindings :: SLS.IndexArrayMap -> SBC.StanBuilderM md gq a -> SBC.StanBuilderM md gq a
extendUseBindings ubs' m = do
  oldBindings <- SBC.indexBindings <$> get
  modify $ modifyIndexBindings (\lc -> lc {SLS.indexes = Map.union ubs' (SLS.indexes lc)})
  a <- m
  modify $ modifyIndexBindings $ const oldBindings
  return a

withDeclBindings :: SLS.IndexSizeMap -> SBC.StanBuilderM md gq a -> SBC.StanBuilderM md gq a
withDeclBindings dbs m = do
  oldBindings <- SBC.indexBindings <$> get
  modify $ modifyIndexBindings (\lc -> lc {SLS.sizes = dbs})
  a <- m
  modify $ modifyIndexBindings $ const oldBindings
  return a

extendDeclBindings :: SLS.IndexSizeMap -> SBC.StanBuilderM md gq a -> SBC.StanBuilderM md gq a
extendDeclBindings dbs' m = do
  oldBindings <- SBC.indexBindings <$> get
  modify $ modifyIndexBindings (\lc -> lc {SLS.sizes = Map.union dbs' (SLS.sizes lc)})
  a <- m
  modify $ modifyIndexBindings $ const oldBindings
  return a

addScopedDeclBindings :: SLS.IndexSizeMap -> SBC.StanBuilderM env d a -> SBC.StanBuilderM env d a
addScopedDeclBindings dbs' m = do
  oldBindings <- SBC.indexBindings <$> get
  modify $ modifyIndexBindings (\lc -> lc {SLS.sizes = Map.union dbs' (SLS.sizes lc)})
  a <- m
  modify $ modifyIndexBindings $ const oldBindings
  return a

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


modifyConstJson :: SBC.InputDataType -> (SBC.JSONSeriesFold () -> SBC.JSONSeriesFold ()) -> SBC.BuilderState md gq -> SBC.BuilderState md gq
modifyConstJson idt f bs = case idt of
  SBC.ModelData -> bs { SBC.constModelJSON = f (SBC.constModelJSON bs)}
  SBC.GQData -> bs { SBC.constGQJSON = f (SBC.constGQJSON bs)}
--(BuilderState dvs ibs mrbs gqrbs cj hfs c) = BuilderState dvs ibs mrbs gqrbs (f cj) hfs c

addConstJson :: SBC.InputDataType -> SBC.JSONSeriesFold () -> SBC.BuilderState md gq -> SBC.BuilderState md gq
addConstJson idt jf = modifyConstJson idt (<> jf)

modifyFunctionNames :: (Set Text -> Set Text) -> SBC.BuilderState md gq -> SBC.BuilderState md gq
modifyFunctionNames f bs = bs { SBC.hasFunctions = f (SBC.hasFunctions bs)}
--(BuilderState dv vbs mrb gqrb cj hf c) = BuilderState dv vbs mrb gqrb cj (f hf) c


addFunctionsOnce :: Text -> SBC.StanBuilderM md gq () -> SBC.StanBuilderM md gq ()
addFunctionsOnce functionsName fCode = do
--  (BuilderState vars ibs rowBuilders cj fsNames code) <- get
  fsNames <- gets SBC.hasFunctions
  if functionsName `Set.member` fsNames
    then return ()
    else (do
             inBlock SLP.SBFunctions fCode
             modify $ modifyFunctionNames $ Set.insert functionsName
         )

addFunctionOnce :: Traversable g
                => SLF.Function rt ats
                -> SLF.TypedArgNames ats
                -> (SLE.ExprList ats -> (g SLS.UStmt, SLE.UExpr rt))
                -> SBC.StanBuilderM md gq (SLF.Function rt ats)
addFunctionOnce f@(SLF.Function fn _ _) argNames fBF = do
  fsNames <- gets SBC.hasFunctions
  when (not $  fn `Set.member` fsNames) $ do
    inBlock SLP.SBFunctions $ addStmtToCode $ SLS.function f argNames fBF
    modify $ modifyFunctionNames (Set.insert fn)
  pure f
addFunctionOnce f@(SLF.IdentityFunction _) _ _ = pure f

addDensityOnce :: Traversable g
               => SLF.Density gt ats
               -> SLF.TypedArgNames (gt ': ats)
               -> (SLE.ExprList (gt ': ats) -> (g SLS.UStmt, SLE.UExpr SLT.EReal))
               -> SBC.StanBuilderM md gq (SLF.Density gt ats)
addDensityOnce f@(SLF.Density fn _ _) argNames fBF = do
  fsNames <- gets SBC.hasFunctions
  when (not $  fn `Set.member` fsNames) $ do
    inBlock SLP.SBFunctions $ addStmtToCode $ SLS.function (SLF.densityAsFunction f) argNames fBF
    modify $ modifyFunctionNames (Set.insert fn)
  pure f

getAndEmptyProgram :: SBC.StanBuilderM md gq SLP.StanProgram
getAndEmptyProgram = do
  (SBC.StanCode cb p) <- gets SBC.code
  modify (\bs -> bs { SBC.code = SBC.StanCode cb SLP.emptyStanProgram})
  pure p

addProgramBelow :: SLP.StanProgram -> SBC.StanBuilderM md gq ()
addProgramBelow pBelow = do
  (SBC.StanCode cb pTop) <- gets SBC.code
  modify (\bs -> bs { SBC.code = SBC.StanCode cb $ pTop <> pBelow})

addCodeAbove :: SBC.StanBuilderM md gq a -> SBC.StanBuilderM md gq a
addCodeAbove ma = do
  pBelow <- getAndEmptyProgram
  a <- ma
  addProgramBelow pBelow
  pure a
