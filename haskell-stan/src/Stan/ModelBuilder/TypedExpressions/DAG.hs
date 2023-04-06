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

module Stan.ModelBuilder.TypedExpressions.DAG
  (
    module Stan.ModelBuilder.TypedExpressions.DAG
  , module Stan.ModelBuilder.TypedExpressions.DAGTypes
  )
  where

import Prelude hiding (All)
import qualified Stan.ModelBuilder as SB

import qualified Stan.ModelBuilder.TypedExpressions.DAGTypes as DT
import Stan.ModelBuilder.TypedExpressions.DAGTypes
import qualified Stan.ModelBuilder.TypedExpressions.Types as TE
import qualified Stan.ModelBuilder.TypedExpressions.TypedList as TE
import qualified Stan.ModelBuilder.TypedExpressions.Statements as TE
import qualified Stan.ModelBuilder.TypedExpressions.StanFunctions as TE
import Stan.ModelBuilder.TypedExpressions.Recursion (hfmap, K(..))

import qualified Data.Dependent.Map as DM
import qualified Data.Dependent.Sum as DM
import qualified Data.Graph as Gr
import qualified Control.Foldl as FL
import Data.Vec.Lazy (Vec(..))


-- put Builder in collection and return a tag to add to anything wanting to use the parameter as a dependency

addBuildParameter :: DT.BuildParameter t -> SB.StanBuilderM md gq (DT.ParameterTag t)
addBuildParameter bp = do
  bpc <- gets SB.parameterCollection
  (bpc', ttn) <- SB.stanBuildEither $ DT.addBuildParameterE bp bpc
  isNew <- SB.declare (DT.bParameterName bp) (DT.bParameterStanType bp)
  when (not isNew)
    $ SB.stanBuildError
    $ "addBuildParameter: parameter name (\"" <> bParameterName bp <> "\") already in use as variable."
  let f bs = bs { SB.parameterCollection = bpc'}
  modify f
  return ttn

data PhantomP where
  PhantomP :: forall t. DT.BuildParameter t -> PhantomP

withPhantomP :: PhantomP -> (forall t. DT.BuildParameter t -> r) -> r
withPhantomP (PhantomP p) f = f p

-- we build a graph, using wrapped parameters as nodes and names as keys
-- topologically sort it
-- return the list of parameters in order we can build them.
depOrderedPParameters :: DT.BParameterCollection -> [PhantomP]
depOrderedPParameters pc =  (\(pp, _, _) -> pp) . vToBuildInfo <$> Gr.topSort pGraph where
  parameterNameM :: DT.Parameter t -> Maybe TE.StanName
  parameterNameM = \case
    DT.GivenP _ -> Nothing
    DT.BuildP ttn -> Just $ DT.taggedParameterName ttn
    DT.MappedP _ p -> parameterNameM p
  bParameterNames :: DT.Parameters ts -> [TE.StanName]
  bParameterNames = catMaybes . TE.typedKToList . hfmap (K . parameterNameM)
  dSumToGBuildInfo :: DM.DSum DT.ParameterTag DT.BuildParameter -> (PhantomP, TE.StanName, [TE.StanName])
  dSumToGBuildInfo (_ DM.:=> bp) = (PhantomP bp, DT.bParameterName bp, withBPDeps bp bParameterNames)
  (pGraph, vToBuildInfo, _) = Gr.graphFromEdges . fmap dSumToGBuildInfo . DM.toList $ DT.pdm pc
--  orderedVList = Gr.topSort pGraph


declareAndAddCode :: SB.StanBlock -> TE.NamedDeclSpec t -> DT.DeclCode t -> SB.StanBuilderM md gq (TE.UExpr t)
declareAndAddCode sb nds dc =
  SB.inBlock sb
  $ case dc of
      DT.DeclRHS e -> do
        SB.addStmtToCodeTop $ TE.declareAndAssignN nds e
        pure $ TE.namedE (TE.declName nds) (TE.sTypeFromStanType $ TE.declType $ TE.decl nds)
      DT.DeclCodeF sF -> do
        let declS = TE.declareN nds
            v = TE.namedE (TE.declName nds) (TE.sTypeFromStanType $ TE.declType $ TE.decl nds)
        SB.addStmtsToCodeTop $ declS : TE.writerL' (sF v)
        pure v

addParameterToCodeAndMap :: DM.DMap DT.ParameterTag TE.UExpr
                         -> PhantomP
                         -> SB.StanBuilderM md gq (DM.DMap DT.ParameterTag TE.UExpr)
addParameterToCodeAndMap eMap (PhantomP bp) = do
  v <- case bp of
    DT.TransformedDataP (DT.TData nds ftds tds desF) -> do
      traverse_ (\(DT.FunctionToDeclare n fs) -> SB.addFunctionsOnce n $ SB.addStmtToCodeTop fs) $ reverse ftds
      tdEs <- SB.stanBuildEither $ DT.lookupTDataExpressions tds eMap
      declareAndAddCode SB.SBTransformedData nds $ desF tdEs
    DT.UntransformedP nds ftds ps codeF -> do
      traverse_ (\(DT.FunctionToDeclare n fs) -> SB.addFunctionsOnce n $ SB.addStmtToCodeTop fs) $ reverse ftds
      psE <- SB.stanBuildEither $ DT.lookupParameterExpressions ps eMap
      SB.inBlock SB.SBParameters $ SB.addStmtToCodeTop $ TE.declareN nds --SB.stanDeclareN nds
      let v =  TE.namedE (TE.declName nds) (TE.sTypeFromStanType $ TE.declType $ TE.decl nds)
      SB.inBlock SB.SBModel $ SB.addStmtsToCodeTop $ TE.writerL' $ codeF psE v --TE.sample v d psE
      pure v
    DT.TransformedP nds ftds pq tpl tpDesF pr codeF -> do
      traverse_ (\(DT.FunctionToDeclare n fs) -> SB.addFunctionsOnce n $ SB.addStmtToCodeTop fs) $ reverse ftds
      pqEs <- SB.stanBuildEither $ DT.lookupParameterExpressions pq eMap
      prEs <- SB.stanBuildEither $ DT.lookupParameterExpressions pr eMap
      let modelBlockCodeAndVar = TE.writerL $ case tpDesF pqEs of
            DT.DeclRHS e -> do
              v' <- TE.declareRHSNW nds e
              codeF prEs v'
              pure v'
            DT.DeclCodeF cF -> do
              v' <- TE.declareNW nds
              cF v'
              codeF prEs v'
              pure v'
      case tpl of
        DT.TransformedParametersBlock -> do
          v <- declareAndAddCode SB.SBTransformedParameters nds $ tpDesF pqEs
          SB.inBlock SB.SBModel $ SB.addStmtsToCodeTop $ TE.writerL' $ codeF prEs v
          pure v
        DT.ModelBlock -> do
          let (c, v) = modelBlockCodeAndVar
          SB.inBlock SB.SBModel $ SB.addStmtsToCodeTop c
          pure v
        DT.ModelBlockLocal p -> do
          let (c, v) = modelBlockCodeAndVar
          SB.inBlock SB.SBModel $ SB.addStmtToCodeTop $ TE.scoped c
          pure $ DT.parameterExpr p

{-    DT.ModelP nds ftds pq tpDesF -> do
      traverse_ (\(DT.FunctionToDeclare n fs) -> SB.addFunctionsOnce n $ SB.addStmtToCodeTop fs) $ reverse ftds
      pqEs <- SB.stanBuildEither $ DT.lookupParameterExpressions pq eMap
      declareAndAddCode SB.SBModel nds $ tpDesF pqEs
-}
  return $ DT.addBuiltExpressionToMap bp v eMap

-- reverse here because we are adding from top, so
addAllParametersInCollection :: forall md gq. DT.BParameterCollection -> SB.StanBuilderM md gq ()
addAllParametersInCollection = FL.foldM makeFold . reverse . depOrderedPParameters
  where makeFold :: FL.FoldM (SB.StanBuilderM x y) PhantomP ()
        makeFold = FL.FoldM addParameterToCodeAndMap (pure DM.empty) (const $ pure ())

rawName :: Text -> Text
rawName t = t <> "_raw"
--

-- should be used in place of runStanBuilder
runStanBuilderDAG :: forall md gq a .
                     md
                  -> gq
                  -> SB.StanGroupBuilderM md gq ()
                  -> SB.StanBuilderM md gq a
                  -> Either Text (SB.BuilderState md gq, a)
runStanBuilderDAG md gq sgb sb =
  let sb' :: SB.StanBuilderM md gq a
      sb' = do
        a <- sb
        bpc <- gets SB.parameterCollection
        addAllParametersInCollection bpc
        return a
      builderState = SB.runStanGroupBuilder sgb md gq
      (resE, bs) = usingState builderState . runExceptT $ SB.unStanBuilderM sb'
  in fmap (bs,) resE



exprListToParameters :: TE.ExprList ts  -> DT.Parameters ts
exprListToParameters = hfmap DT.GivenP

-- some useful special cases

-- Only dependencies are parameters to prior density
simpleParameterWA :: TE.NamedDeclSpec t -> TE.DensityWithArgs t -> SB.StanBuilderM md gq (ParameterTag t)
simpleParameterWA nds = TE.withDWA (\d as -> simpleParameter nds (exprListToParameters as) d)


simpleParameter :: TE.NamedDeclSpec t -> DT.Parameters ts -> TE.Density t ts -> SB.StanBuilderM md gq (ParameterTag t)
simpleParameter nds ps d = addBuildParameter $ DT.UntransformedP nds [] ps (\qs t -> TE.addStmt $ TE.sample t d qs)


addCenteredHierarchical :: TE.NamedDeclSpec t
                        -> Parameters args
                        -> TE.Density t args
                        -> SB.StanBuilderM md gq (ParameterTag t)
addCenteredHierarchical nds ps d = addBuildParameter
                                  $ UntransformedP nds [] ps
                                  $ \argEs e -> TE.addStmt $ TE.sample e d argEs


addNonCenteredParameter :: TE.NamedDeclSpec t
                     -> DT.Parameters ts
                     -> DT.TransformedParameterLocation t
                     -> TE.DeclSpec t
                     -> TE.Density t ts
                     -> DT.Parameters qs
                     -> (TE.ExprList qs -> TE.UExpr t -> TE.UExpr t)
                     -> SB.StanBuilderM md gq (DT.ParameterTag t)
addNonCenteredParameter nds ps tpl rawDS rawD qs eF = do
  let rawNDS = TE.NamedDeclSpec (rawName $ TE.declName nds) rawDS
  rawPT <- simpleParameter rawNDS ps rawD
  let tpDES (rV TE.:> qsE) = DeclRHS $ eF qsE rV
  addBuildParameter $ DT.simpleTransformedP nds [] (DT.BuildP rawPT TE.:> qs) tpl tpDES

-- Only use if density uses constant args. E.g., stdNormal.
-- If it uses named parameters,
-- those should be dependencies, so use `nonCenteredParameters'
simpleNonCentered :: TE.NamedDeclSpec t
                  -> DT.TransformedParameterLocation t
                  -> TE.DeclSpec t
                  -> TE.DensityWithArgs t
                  -> DT.Parameters qs
                  -> (TE.ExprList qs -> TE.UExpr t -> TE.UExpr t)
                  -> SB.StanBuilderM md gq (DT.ParameterTag t)
simpleNonCentered nds tpl rawDS (TE.DensityWithArgs d tsE) =
  addNonCenteredParameter nds (exprListToParameters tsE) tpl rawDS d

addIndependentPriorP :: TE.NamedDeclSpec t -> TE.DensityWithArgs t -> SB.StanBuilderM md gq (ParameterTag t)
addIndependentPriorP nds (TE.DensityWithArgs d dArgs) =
  addBuildParameter
  $ UntransformedP nds [] (exprListToParameters dArgs)
  $ \argEs e -> TE.addStmt $ TE.sample e d argEs

addNonCenteredHierarchicalS :: TE.NamedDeclSpec t
                            -> DT.TransformedParameterLocation t
                            -> Parameters ts
                            -> TE.DensityWithArgs t
                            -> (TE.ExprList ts -> TE.UExpr t -> TE.UExpr t)
                            -> SB.StanBuilderM md gq (ParameterTag t)
addNonCenteredHierarchicalS nds tpl ps (TE.DensityWithArgs d dArgs) =
  addNonCenteredParameter nds (exprListToParameters dArgs) tpl (TE.decl nds) d ps

addTransformedHP :: TE.NamedDeclSpec t
                 -> DT.TransformedParameterLocation t
                 -> Maybe [TE.VarModifier TE.UExpr (TE.ScalarType t)]
                 -> TE.DensityWithArgs t
                 -> (TE.UExpr t -> TE.UExpr t)
                 -> SB.StanBuilderM md gq (ParameterTag t)
addTransformedHP nds tpl rawCsM rawPrior fromRawF = do
  let TE.DeclSpec st dims _ = TE.decl nds
      rawNDS = TE.NamedDeclSpec (rawName $ TE.declName nds) $ maybe (TE.decl nds) (TE.DeclSpec st dims) rawCsM
  rawPT <- addIndependentPriorP rawNDS rawPrior
  addBuildParameter $ simpleTransformedP nds [] (BuildP rawPT TE.:> TE.TNil) tpl (\(e TE.:> TE.TNil) -> DeclRHS $ fromRawF e) -- (ExprList qs -> DeclCode t)

iidMatrixP :: TE.NamedDeclSpec TE.EMat
          -> [FunctionToDeclare]
          -> Parameters qs
          -> TE.Density TE.ECVec qs
          -> SB.StanBuilderM md gq (DT.ParameterTag TE.EMat)
iidMatrixP nds ftd ps d = addBuildParameter
                          $ UntransformedP nds ftd ps
                          $ \qs m -> TE.addStmt $ TE.sample (TE.functionE TE.to_vector (m TE.:> TE.TNil)) d qs

-- this puts the prior on the raw parameters
withIIDRawMatrix :: TE.NamedDeclSpec TE.EMat
                 -> DT.TransformedParameterLocation TE.EMat
                 -> Maybe [TE.VarModifier TE.UExpr TE.EReal] -- constraints on raw
                 -> TE.DensityWithArgs TE.ECVec -- prior density on raw
                 -> DT.Parameters qs
                 -> (TE.ExprList qs -> TE.MatrixE -> TE.MatrixE)
                 -> SB.StanBuilderM md gq (DT.ParameterTag TE.EMat)
withIIDRawMatrix nds tpl rawCsM dwa qs f = do
 let TE.DeclSpec _ (rowsE ::: colsE ::: VNil) _ = TE.decl nds
     rawNDS = TE.NamedDeclSpec (rawName $ TE.declName nds) $ TE.matrixSpec rowsE colsE $ fromMaybe [] rawCsM
 rawPT <- TE.withDWA (\d tl -> iidMatrixP rawNDS [] (exprListToParameters tl) d) dwa
 addBuildParameter $ simpleTransformedP nds [] (BuildP rawPT TE.:> qs) tpl (\(rmE TE.:> qsE) -> DeclRHS $ f qsE rmE)

{-
-- this puts the prior on the transformed matrix
withIIDTransformedMatrix :: TE.NamedDeclSpec TE.EMat
                         -> Maybe [TE.VarModifier TE.UExpr TE.EReal] --constraints on raw
                         -> TE.DensityWithArgs TE.ECVec -- prior density on transformed
                         -> DT.Parameters qs
                         -> (TE.ExprList qs -> TE.MatrixE -> TE.MatrixE)
                         -> SB.StanBuilderM md gq (DT.ParameterTag TE.EMat)
withIIDTransformedMatrix nds rawCsM dwa qs f = do
 let TE.DeclSpec _ (rowsE ::: colsE ::: VNil) cs = TE.decl nds
     rawNDS = TE.NamedDeclSpec (rawName $ TE.declName nds) $ TE.matrixSpec rowsE colsE $ fromMaybe [] rawCsM
 rawPT <- TE.withDWA (\d tl -> iidMatrixP rawNDS [] (exprListToParameters tl) d) dwa
 addBuildParameter $ TransformedP nds [] (BuildP rawPT TE.:> qs) (\(rmE TE.:> qsE) -> DeclRHS $ f qsE rmE)
-}
