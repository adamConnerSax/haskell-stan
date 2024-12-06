{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

module Stan.Builder.Parameters
  (
    module Stan.Builder.Parameters
  , module Stan.Builder.ParameterTypes
  )
  where

import Prelude hiding (All)
import qualified Stan.Builder.CoreTypes as SBC
import qualified Stan.Builder.Build as SB
import qualified Stan.Builder.ParameterTypes as PT

import Stan.Builder.ParameterTypes (DeclCode(..)
                                   , BuildParameter(..)
                                   , TData(..)
                                   , TransformedParameterLocation(..)
                                   , Parameter
                                   , ParameterTag
                                   , Parameters
                                   , build, given
                                   , parameterExpr
                                   )
import qualified Stan.Language.Program as SLP
import qualified Stan.Language.Types as SLT
import qualified Stan.Language.TypedList as SLTL
import Stan.Language.TypedList (TypedList(..))
import qualified Stan.Language.Statements as SLS
import qualified Stan.Language.Functions as SLF

import qualified Control.Monad.State as St
--import qualified Stan.Language.StanFunctions as TE
import Stan.Language.Recursion (hfmap, K(..))

import qualified Data.Dependent.Map as DM
import qualified Data.Dependent.Sum as DM
import qualified Data.Graph as Gr
import qualified Control.Foldl as FL
import Data.Vec.Lazy (Vec(..))
-- put Builder in collection and return a tag to add to anything wanting to use the parameter as a dependency

addBuildParameter :: PT.BuildParameter t -> SBC.StanBuilderM md gq (PT.Parameter t)
addBuildParameter bp = do
  bpc <- gets SBC.parameterCollection
  (bpc', ttn) <- SBC.stanBuildEither $ PT.addBuildParameterE bp bpc
  isNew <- SB.declare (PT.bParameterName bp) (PT.bParameterStanType bp)
  when (not isNew)
    $ SBC.stanBuildError
    $ "addBuildParameter: parameter name (\"" <> PT.bParameterName bp <> "\") already in use as variable."
  let f bs = bs { SBC.parameterCollection = bpc'}
  modify f
  pure $ build ttn

data PhantomP where
  PhantomP :: forall t. PT.BuildParameter t -> PhantomP

withPhantomP :: PhantomP -> (forall t. PT.BuildParameter t -> r) -> r
withPhantomP (PhantomP p) f = f p

-- we build a graph, using wrapped parameters as nodes and names as keys
-- topologically sort it
-- return the list of parameters in order we can build them.
depOrderedPParameters :: PT.BParameterCollection -> [PhantomP]
depOrderedPParameters pc =  (\(pp, _, _) -> pp) . vToBuildInfo <$> Gr.topSort pGraph where
  parameterNameM :: PT.Parameter t -> Maybe SLS.StanName
  parameterNameM = \case
    PT.GivenP _ -> Nothing
    PT.BuildP ttn -> Just $ PT.taggedParameterName ttn
    PT.MappedP _ p -> parameterNameM p
  bParameterNames :: PT.Parameters ts -> [SLS.StanName]
  bParameterNames = catMaybes . SLTL.typedKToList . hfmap (K . parameterNameM)
  dSumToGBuildInfo :: DM.DSum PT.ParameterTag PT.BuildParameter -> (PhantomP, SLS.StanName, [SLS.StanName])
  dSumToGBuildInfo (_ DM.:=> bp) = (PhantomP bp, PT.bParameterName bp, PT.withBPDeps bp bParameterNames)
  (pGraph, vToBuildInfo, _) = Gr.graphFromEdges . fmap dSumToGBuildInfo . DM.toList $ PT.pdm pc
--  orderedVList = Gr.topSort pGraph

addDAGStmt :: SLS.UStmt -> SBC.StanBuilderM md gq ()
addDAGStmt = SB.addStmtToCode

addDAGStmts :: Traversable f => f SLS.UStmt -> SBC.StanBuilderM md gq ()
addDAGStmts = SB.addStmtsToCode

declareAndAddCode :: SLP.StanBlock -> SLS.NamedDeclSpec t -> PT.DeclCode t -> SBC.StanBuilderM md gq (SLS.UExpr t)
declareAndAddCode sb nds dc =
  SB.inBlock sb
  $ case dc of
      PT.DeclRHS e -> do
        addDAGStmt $ SLS.declareAndAssignN nds e
        pure $ SLS.namedE (SLS.declName nds) (SLT.sTypeFromStanType $ SLS.declType $ SLS.decl nds)
      PT.DeclCodeF sF -> do
        let declS = SLS.declareN nds
            v = SLS.namedE (SLS.declName nds) (SLT.sTypeFromStanType $ SLS.declType $ SLS.decl nds)
        addDAGStmts $ declS : SLS.writerL' (sF v)
        pure v

addParameterToCodeAndMap :: DM.DMap PT.ParameterTag SLS.UExpr
                         -> PhantomP
                         -> SBC.StanBuilderM md gq (DM.DMap PT.ParameterTag SLS.UExpr)
addParameterToCodeAndMap eMap (PhantomP bp) = do
  vM <- case bp of
    PT.TransformedDataP (PT.TData nds ftds tds desF) -> do
      traverse_ (\(PT.FunctionToDeclare n fs) -> SB.addFunctionsOnce n $ addDAGStmt fs) $ reverse ftds
      tdEs <- SBC.stanBuildEither $ PT.lookupTDataExpressions tds eMap
      fmap Just $ (declareAndAddCode SLP.SBTransformedData nds $ desF tdEs)
    PT.UntransformedP nds ftds ps codeF -> do
      traverse_ (\(PT.FunctionToDeclare n fs) -> SB.addFunctionsOnce n $ addDAGStmt fs) $ reverse ftds
      psE <- SBC.stanBuildEither $ PT.lookupParameterExpressions ps eMap
      SB.inBlock SLP.SBParameters $ addDAGStmt $ SLS.declareN nds --SB.stanDeclareN nds
      let v =  SLS.namedE (SLS.declName nds) (SLT.sTypeFromStanType $ SLS.declType $ SLS.decl nds)
      SB.inBlock SLP.SBModel $ addDAGStmts $ SLS.writerL' $ codeF psE v --TE.sample v d psE
      pure $ Just v
    PT.TransformedP nds ftds pq tpl tpDesF pr codeF -> do
      traverse_ (\(PT.FunctionToDeclare n fs) -> SB.addFunctionsOnce n $ addDAGStmt fs) $ reverse ftds
      pqEs <- SBC.stanBuildEither $ PT.lookupParameterExpressions pq eMap
      prEs <- SBC.stanBuildEither $ PT.lookupParameterExpressions pr eMap
      let modelBlockCodeAndVar = SLS.writerL $ case tpDesF pqEs of
            PT.DeclRHS e -> do
              v' <- SLS.declareRHSNW nds e
              codeF prEs v'
              pure v'
            PT.DeclCodeF cF -> do
              v' <- SLS.declareNW nds
              cF v'
              codeF prEs v'
              pure v'
      case tpl of
        PT.TransformedParametersBlock -> do
          v <- declareAndAddCode SLP.SBTransformedParameters nds $ tpDesF pqEs
          SB.inBlock SLP.SBModel $ addDAGStmts $ SLS.writerL' $ codeF prEs v
          pure $ Just v
        PT.ModelBlock -> do
          let (c, v) = modelBlockCodeAndVar
          SB.inBlock SLP.SBModel $ addDAGStmts c
          pure $ Just v
        PT.ModelBlockLocal -> do
          let (c, _) = modelBlockCodeAndVar
          SB.inBlock SLP.SBModel $ addDAGStmt $ SLS.scoped c
          pure Nothing -- we add nothing to the map since the expression we built here is local and can't be used elsewhere

  let newMapF = maybe id (PT.addBuiltExpressionToMap bp) vM
  pure $ newMapF eMap

-- reverse here because we are adding from top, so
addAllParametersInCollection :: forall md gq. PT.BParameterCollection -> SBC.StanBuilderM md gq ()
addAllParametersInCollection = FL.foldM makeFold . reverse . depOrderedPParameters
  where makeFold :: FL.FoldM (SBC.StanBuilderM x y) PhantomP ()
        makeFold = FL.FoldM addParameterToCodeAndMap (pure DM.empty) (const $ pure ())

rawName :: Text -> Text
rawName t = t <> "_raw"
--

-- should be used in place of runStanBuilder
runStanBuilderDAG :: forall md gq a .
                     md
                  -> gq
                  -> SBC.StanGroupBuilderM md gq ()
                  -> SBC.StanBuilderM md gq a
                  -> Either Text (SBC.BuilderState md gq, a)
runStanBuilderDAG md gq sgb sb =
  let sb' :: SBC.StanBuilderM md gq a
      sb' = do
        a <- sb
        -- we need the parameter code to come before anything written assuming it exists
        -- so, shenanigans
        SB.addCodeAbove $ do
          bpc <- gets SBC.parameterCollection
          addAllParametersInCollection bpc
        return a
      builderState = SBC.runStanGroupBuilder sgb md gq
      (resE, bs) = usingState builderState . runExceptT $ SBC.unStanBuilderM sb'
  in fmap (bs,) resE

exprListToParameters :: SLS.ExprList ts  -> PT.Parameters ts
exprListToParameters = hfmap PT.GivenP

-- some useful special cases
modelP ::  SLS.NamedDeclSpec t
         -> [PT.FunctionToDeclare]
         -> PT.Parameters qs
         -> (SLS.ExprList qs -> PT.DeclCode t)
         -> PT.BuildParameter t
modelP nds ftds pq tpDesF = PT.TransformedP nds ftds pq PT.ModelBlock tpDesF TNil (\_ _ -> pure ())

simpleTransformedP :: SLS.NamedDeclSpec t
                   -> [PT.FunctionToDeclare]
                   -> PT.Parameters qs -- parameters for transformation
                   -> PT.TransformedParameterLocation
                   -> (SLS.ExprList qs -> PT.DeclCode t) -- code for transformed parameters blockBuildParameter t
                   -> PT.BuildParameter t
simpleTransformedP nds ftd ps tpl declCodeF = PT.TransformedP nds ftd ps tpl declCodeF TNil (\_ _ -> pure ())


-- Only dependencies are parameters to prior density
simpleParameterWA :: SLS.NamedDeclSpec t -> SLS.DensityWithArgs t -> SBC.StanBuilderM md gq (PT.Parameter t)
simpleParameterWA nds = SLS.withDWA (\d as -> simpleParameter nds (exprListToParameters as) d)


simpleParameter :: SLS.NamedDeclSpec t -> PT.Parameters ts -> SLF.Density t ts -> SBC.StanBuilderM md gq (PT.Parameter t)
simpleParameter nds ps d = addBuildParameter $ PT.UntransformedP nds [] ps (\qs t -> SLS.addStmt $ SLS.sample t d qs)


addCenteredHierarchical :: SLS.NamedDeclSpec t
                        -> PT.Parameters args
                        -> SLF.Density t args
                        -> SBC.StanBuilderM md gq (PT.Parameter t)
addCenteredHierarchical nds ps d = addBuildParameter
                                  $ PT.UntransformedP nds [] ps
                                  $ \argEs e -> SLS.addStmt $ SLS.sample e d argEs


addNonCenteredParameter :: SLS.NamedDeclSpec t
                        -> PT.Parameters ts
                        -> PT.TransformedParameterLocation
                        -> SLS.DeclSpec t
                        -> SLF.Density t ts
                        -> PT.Parameters qs
                        -> (SLS.ExprList qs -> SLS.UExpr t -> SLS.UExpr t)
                        -> SBC.StanBuilderM md gq (PT.Parameter t)
addNonCenteredParameter nds ps tpl rawDS rawD qs eF = do
  let rawNDS = SLS.NamedDeclSpec (rawName $ SLS.declName nds) rawDS
  rawP <- simpleParameter rawNDS ps rawD
  let tpDES (rV :> qsE) = PT.DeclRHS $ eF qsE rV
  addBuildParameter $ simpleTransformedP nds [] (rawP :> qs) tpl tpDES


-- Only use if density uses constant args. E.g., stdNormal.
-- If it uses named parameters,
-- those should be dependencies, so use `nonCenteredParameters'
simpleNonCentered :: SLS.NamedDeclSpec t
                  -> PT.TransformedParameterLocation
                  -> SLS.DeclSpec t
                  -> SLS.DensityWithArgs t
                  -> PT.Parameters qs
                  -> (SLS.ExprList qs -> SLS.UExpr t -> SLS.UExpr t)
                  -> SBC.StanBuilderM md gq (PT.Parameter t)
simpleNonCentered nds tpl rawDS (SLS.DensityWithArgs d tsE) =
  addNonCenteredParameter nds (exprListToParameters tsE) tpl rawDS d

addIndependentPriorP :: SLS.NamedDeclSpec t -> SLS.DensityWithArgs t -> SBC.StanBuilderM md gq (PT.Parameter t)
addIndependentPriorP nds (SLS.DensityWithArgs d dArgs) =
  addBuildParameter
  $ PT.UntransformedP nds [] (exprListToParameters dArgs)
  $ \argEs e -> SLS.addStmt $ SLS.sample e d argEs

addNonCenteredHierarchicalS :: SLS.NamedDeclSpec t
                            -> PT.TransformedParameterLocation
                            -> PT.Parameters ts
                            -> SLS.DensityWithArgs t
                            -> (SLS.ExprList ts -> SLS.UExpr t -> SLS.UExpr t)
                            -> SBC.StanBuilderM md gq (PT.Parameter t)
addNonCenteredHierarchicalS nds tpl ps (SLS.DensityWithArgs d dArgs) =
  addNonCenteredParameter nds (exprListToParameters dArgs) tpl (SLS.decl nds) d ps

addTransformedHP :: SLS.NamedDeclSpec t
                 -> PT.TransformedParameterLocation
                 -> Maybe [SLS.VarModifier SLS.UExpr (SLT.ScalarType t)]
                 -> SLS.DensityWithArgs t
                 -> (SLS.UExpr t -> SLS.UExpr t)
                 -> SBC.StanBuilderM md gq (PT.Parameter t)
addTransformedHP nds tpl rawCsM rawPrior fromRawF = do
  case SLS.decl nds of
    SLS.DeclSpec st dims _ -> do
      let rawNDS = SLS.NamedDeclSpec (rawName $ SLS.declName nds) $ maybe (SLS.decl nds) (SLS.DeclSpec st dims) rawCsM
      rawP <- addIndependentPriorP rawNDS rawPrior
      addBuildParameter $ simpleTransformedP nds [] (rawP :> TNil) tpl (\(e :> TNil) -> PT.DeclRHS $ fromRawF e) -- (ExprList qs -> DeclCode t)
    SLS.ArraySpec n arrDims ds -> do
      let rawNDS = SLS.NamedDeclSpec (rawName $ SLS.declName nds) $ maybe (SLS.decl nds) (\vms -> SLS.replaceDeclVMs vms (SLS.ArraySpec n arrDims ds)) rawCsM
      rawP <- addIndependentPriorP rawNDS rawPrior
      addBuildParameter $ simpleTransformedP nds [] (rawP :> TNil) tpl (\(e :> TNil) -> PT.DeclRHS $ fromRawF e) -- (ExprList qs -> DeclCode t)

iidMatrixP :: SLS.NamedDeclSpec SLT.EMat
          -> [PT.FunctionToDeclare]
          -> PT.Parameters qs
          -> SLF.Density SLT.ECVec qs
          -> SBC.StanBuilderM md gq (PT.Parameter SLT.EMat)
iidMatrixP nds ftd ps d = addBuildParameter $ iidMatrixBP nds ftd ps d


iidMatrixBP :: SLS.NamedDeclSpec SLT.EMat
            -> [PT.FunctionToDeclare]
            -> PT.Parameters qs
            -> SLF.Density SLT.ECVec qs
            -> PT.BuildParameter SLT.EMat
iidMatrixBP nds ftd ps d = PT.UntransformedP nds ftd ps
                           $ \qs m -> SLS.addStmt $ SLS.sample (SLS.functionE SLT.to_vector (m :> TNil)) d qs

-- this puts the prior on the raw parameters
withIIDRawMatrix :: SLS.NamedDeclSpec SLT.EMat
                 -> PT.TransformedParameterLocation
                 -> Maybe [SLS.VarModifier SLS.UExpr SLT.EReal] -- constraints on raw
                 -> SLS.DensityWithArgs SLT.ECVec -- prior density on raw
                 -> PT.Parameters qs
                 -> (SLS.ExprList qs -> SLS.MatrixE -> SLS.MatrixE)
                 -> SBC.StanBuilderM md gq (PT.Parameter SLT.EMat)
withIIDRawMatrix nds tpl rawCsM dwa qs f = do
 let SLS.DeclSpec _ (rowsE ::: colsE ::: VNil) _ = SLS.decl nds
     rawNDS = SLS.NamedDeclSpec (rawName $ SLS.declName nds) $ SLS.matrixSpec rowsE colsE $ fromMaybe [] rawCsM
 rawP <- SLS.withDWA (\d tl -> iidMatrixP rawNDS [] (exprListToParameters tl) d) dwa
 addBuildParameter $ simpleTransformedP nds [] (rawP :> qs) tpl (\(rmE :> qsE) -> PT.DeclRHS $ f qsE rmE)

{-
-- this puts the prior on the transformed matrix
withIIDTransformedMatrix :: TE.NamedDeclSpec TE.EMat
                         -> Maybe [TE.VarModifier TE.UExpr TE.EReal] --constraints on raw
                         -> TE.DensityWithArgs TE.ECVec -- prior density on transformed
                         -> PT.Parameters qs
                         -> (TE.ExprList qs -> TE.MatrixE -> TE.MatrixE)
                         -> SB.StanBuilderM md gq (PT.ParameterTag TE.EMat)
withIIDTransformedMatrix nds rawCsM dwa qs f = do
 let TE.DeclSpec _ (rowsE ::: colsE ::: VNil) cs = TE.decl nds
     rawNDS = TE.NamedDeclSpec (rawName $ TE.declName nds) $ TE.matrixSpec rowsE colsE $ fromMaybe [] rawCsM
 rawPT <- TE.withDWA (\d tl -> iidMatrixP rawNDS [] (exprListToParameters tl) d) dwa
 addBuildParameter $ TransformedP nds [] (BuildP rawPT TE.:> qs) (\(rmE TE.:> qsE) -> DeclRHS $ f qsE rmE)
-}
