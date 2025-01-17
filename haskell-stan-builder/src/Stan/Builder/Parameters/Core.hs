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
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

module Stan.Builder.Parameters.Core
  (
    module Stan.Builder.Parameters.Core
  )
  where

import Prelude hiding (All)
import qualified Stan.Builder.Core as SBC
import qualified Stan.Builder.Build as SB
import qualified Stan.Builder.BuildRunner as SBR
import qualified Stan.Builder.Parameters.Types as PT

import qualified Stan.Language.Program as SLP
import qualified Stan.Language.Types as SLT
import Stan.Language.Types (TypedList(..))
import qualified Stan.Language.Expression as SLE
import qualified Stan.Language.Expressions as SLE
import qualified Stan.Language.Statement as SLS
import qualified Stan.Language.Statements as SLS
import qualified Stan.Language.CodeWriter as SLC
import qualified Stan.Language.Functions as SLF
import qualified Stan.Functions.Containers as SFC

import Stan.Language.Recursion (hfmap, K(..))

import qualified Data.Dependent.Map as DM
import qualified Data.Dependent.Sum as DM
import qualified Data.Graph as Gr
import qualified Control.Foldl as FL

import Effectful ((:>), Eff)
import qualified Effectful.State.Static.Local as EffS
import qualified Effectful.Fail as EffF
-- put Builder in collection and return a tag to add to anything wanting to use the parameter as a dependency

type ParameterEffs es = (EffF.Fail :> es, EffS.State PT.BParameterCollection :> es)

addBuildParameter :: ParameterEffs es => PT.BuildParameter t -> Eff es (PT.Parameter t)
addBuildParameter bp = do
  bpc <- EffS.get
  (bpc', ttn) <- SBC.buildEither $ PT.addBuildParameterE bp bpc
  EffS.put bpc'
  pure $ PT.build ttn

data PhantomP where
  PhantomP :: forall t. PT.BuildParameter t -> PhantomP

withPhantomP :: PhantomP -> (forall t. PT.BuildParameter t -> r) -> r
withPhantomP (PhantomP p) f = f p

-- we build a graph, using wrapped parameters as nodes and names as keys
-- topologically sort it
-- return the list of parameters in order we can build them.
depOrderedPParameters :: PT.BParameterCollection -> [PhantomP]
depOrderedPParameters pc =  (\(pp, _, _) -> pp) . vToBuildInfo <$> Gr.topSort pGraph where
  parameterNameM :: PT.Parameter t -> Maybe SLT.VarName
  parameterNameM = \case
    PT.GivenP _ -> Nothing
    PT.BuildP ttn -> Just $ PT.taggedParameterName ttn
    PT.MappedP _ p -> parameterNameM p
  bParameterNames :: PT.Parameters ts -> [SLT.VarName]
  bParameterNames = catMaybes . SLT.typedKToList . hfmap (K . parameterNameM)
  dSumToGBuildInfo :: DM.DSum PT.ParameterTag PT.BuildParameter -> (PhantomP, SLT.VarName, [SLT.VarName])
  dSumToGBuildInfo (_ DM.:=> bp) = (PhantomP bp, PT.bParameterName bp, PT.withBPDeps bp bParameterNames)
  (pGraph, vToBuildInfo, _) = Gr.graphFromEdges . fmap dSumToGBuildInfo . DM.toList $ PT.pdm pc
--  orderedVList = Gr.topSort pGraph

{-
addDAGStmt :: (EffF.Fail :> es, EffS.State SBC.StanCode :> es) => SLS.UStmt -> Eff es ()
addDAGStmt = SB.addStmtToCode

addDAGStmts :: (EffS.State SBC.StanCode :> es, Traversable f) => f SLS.UStmt -> Eff es ()
addDAGStmts = SB.addStmtsToCode
-}
declareAndAddCode :: SBC.StanCodeC es => SLP.StanBlock -> SLS.NamedDeclSpec t -> PT.DeclCode t -> Eff es (SLE.UExpr t)
declareAndAddCode sb nds dc =
  case dc of
    PT.DeclRHS e -> do
      SB.addStmtToBlock sb $ SLS.declareAndAssignN nds e
      pure $ SLE.namedE (SLS.declName nds) (SLT.sTypeFromStanType $ SLS.declType $ SLS.decl nds)
    PT.DeclCodeF sF -> do
      let declS = SLS.declareN nds
          v = SLE.namedE (SLS.declName nds) (SLT.sTypeFromStanType $ SLS.declType $ SLS.decl nds)
      SB.addStmtsToBlock sb $ declS : SLC.cwStmtList_ (sF v)
      pure v

addParameterToCodeAndMap :: SBC.StanFunctionsC es
                         => DM.DMap PT.ParameterTag SLE.UExpr
                         -> PhantomP
                         -> Eff es (DM.DMap PT.ParameterTag SLE.UExpr)
addParameterToCodeAndMap eMap (PhantomP bp) = do
  vM <- case bp of
    PT.TransformedDataP (PT.TData nds ftds tds desF) -> do
      traverse_ (\(PT.FunctionToDeclare n fs) -> SB.addFunctionCodeOnce n fs) $ reverse ftds
      tdEs <- SBC.buildEither $ PT.lookupTDataExpressions tds eMap
      Just <$> (declareAndAddCode SLP.SBTransformedData nds $ desF tdEs)
    PT.UntransformedP nds ftds ps codeF -> do
      traverse_ (\(PT.FunctionToDeclare n fs) -> SB.addFunctionCodeOnce n fs) $ reverse ftds
      psE <- SBC.buildEither $ PT.lookupParameterExpressions ps eMap
      SB.addStmtToBlock SLP.SBParameters $ SLS.declareN nds --SB.stanDeclareN nds
      let v =  SLE.namedE (SLS.declName nds) (SLT.sTypeFromStanType $ SLS.declType $ SLS.decl nds)
      SB.addStmtsToBlock SLP.SBModel $ SLC.cwStmtList_ $ codeF psE v --TE.sample v d psE
      pure $ Just v
    PT.TransformedP nds ftds pq tpl tpDesF pr codeF -> do
      traverse_ (\(PT.FunctionToDeclare n fs) -> SB.addFunctionCodeOnce n fs) $ reverse ftds
      pqEs <- SBC.buildEither $ PT.lookupParameterExpressions pq eMap
      prEs <- SBC.buildEither $ PT.lookupParameterExpressions pr eMap
      let modelBlockCodeAndVar = SLC.cwStmtList $ case tpDesF pqEs of
            PT.DeclRHS e -> do
              v' <- SLC.declareRHSNW nds e
              codeF prEs v'
              pure v'
            PT.DeclCodeF cF -> do
              v' <- SLC.declareNW nds
              cF v'
              codeF prEs v'
              pure v'
      case tpl of
        PT.TransformedParametersBlock -> do
          v <- declareAndAddCode SLP.SBTransformedParameters nds $ tpDesF pqEs
          SB.addStmtsToBlock SLP.SBModel $ SLC.cwStmtList_ $ codeF prEs v
          pure $ Just v
        PT.ModelBlock -> do
          let (c, v) = modelBlockCodeAndVar
          SB.addStmtsToBlock SLP.SBModel c
          pure $ Just v
        PT.ModelBlockLocal -> do
          let (c, _) = modelBlockCodeAndVar
          SB.addStmtToBlock SLP.SBModel $ SLS.scoped $ SLS.grouped c
          pure Nothing -- we add nothing to the map since the expression we built here is local and can't be used elsewhere

  let newMapF = maybe id (PT.addBuiltExpressionToMap bp) vM
  pure $ newMapF eMap

-- reverse here because we are adding from top, so
addAllParametersInCollection :: forall es . SBC.StanFunctionsC es
                             => PT.BParameterCollection -> Eff es ()
addAllParametersInCollection = FL.foldM makeFold . reverse . depOrderedPParameters
  where makeFold :: FL.FoldM (Eff es) PhantomP ()
        makeFold = FL.FoldM addParameterToCodeAndMap (pure DM.empty) (const $ pure ())

rawName :: Text -> Text
rawName t = t <> "_raw"
--

-- should be used in place of runStanBuilder
runStanBuilderDAG :: forall a b c .
                     SBC.ModelSource
                  -> SBC.GQSource
                  -> SBC.StanDataBuilderEff SBC.ModelDataT a
                  -> (a -> SBC.StanDataBuilderEff SBC.GQDataT b)
                  -> (a -> b -> SBC.StanModelBuilderEff c)
                  -> Either Text (SBC.BuilderState, [Text], c)
runStanBuilderDAG md gq modelDG gqDGF sbF =
  let sbF' :: a -> b -> SBC.StanModelBuilderEff c
      sbF' a b = do
        c <- sbF a b
        -- we need the parameter code to come before anything written assuming it exists
        -- so, shenanigans
        SB.addCodeAbove $ do
          bpc <- EffS.get @PT.BParameterCollection
          addAllParametersInCollection bpc
        return c
  in SBR.runStanBuilderEff md gq modelDG gqDGF sbF'

exprListToParameters :: SLE.ExprList ts  -> PT.Parameters ts
exprListToParameters = hfmap PT.GivenP

-- some useful special cases
modelP ::  SLS.NamedDeclSpec t
         -> [PT.FunctionToDeclare]
         -> PT.Parameters qs
         -> (SLE.ExprList qs -> PT.DeclCode t)
         -> PT.BuildParameter t
modelP nds ftds pq tpDesF = PT.TransformedP nds ftds pq PT.ModelBlock tpDesF TNil (\_ _ -> pure ())

simpleTransformedP :: SLS.NamedDeclSpec t
                   -> [PT.FunctionToDeclare]
                   -> PT.Parameters qs -- parameters for transformation
                   -> PT.TransformedParameterLocation
                   -> (SLE.ExprList qs -> PT.DeclCode t) -- code for transformed parameters blockBuildParameter t
                   -> PT.BuildParameter t
simpleTransformedP nds ftd ps tpl declCodeF = PT.TransformedP nds ftd ps tpl declCodeF TNil (\_ _ -> pure ())


-- Only dependencies are parameters to prior density
simpleParameterWA :: ParameterEffs es
                  => SLS.NamedDeclSpec t -> SLS.DensityWithArgs t -> Eff es (PT.Parameter t)
simpleParameterWA nds = SLS.withDWA (\d as -> simpleParameter nds (exprListToParameters as) d)


simpleParameter :: ParameterEffs es
                => SLS.NamedDeclSpec t -> PT.Parameters ts -> SLF.Density t ts -> Eff es (PT.Parameter t)
simpleParameter nds ps d = addBuildParameter $ PT.UntransformedP nds [] ps (\qs t -> SLC.addStmt $ SLS.sample t d qs)


addCenteredHierarchical :: ParameterEffs es
                        => SLS.NamedDeclSpec t
                        -> PT.Parameters args
                        -> SLF.Density t args
                        -> Eff es (PT.Parameter t)
addCenteredHierarchical nds ps d = addBuildParameter
                                  $ PT.UntransformedP nds [] ps
                                  $ \argEs e -> SLC.addStmt $ SLS.sample e d argEs


addNonCenteredParameter :: ParameterEffs es
                        => SLS.NamedDeclSpec t
                        -> PT.Parameters ts
                        -> PT.TransformedParameterLocation
                        -> SLS.DeclSpec SLE.UExpr t
                        -> SLF.Density t ts
                        -> PT.Parameters qs
                        -> (SLE.ExprList qs -> SLE.UExpr t -> SLE.UExpr t)
                        -> Eff es (PT.Parameter t)
addNonCenteredParameter nds ps tpl rawDS rawD qs eF = do
  let rawNDS = SLS.NamedDeclSpec (rawName $ SLS.declName nds) rawDS
  rawP <- simpleParameter rawNDS ps rawD
  let tpDES (rV :> qsE) = PT.DeclRHS $ eF qsE rV
  addBuildParameter $ simpleTransformedP nds [] (rawP :> qs) tpl tpDES


-- Only use if density uses constant args. E.g., stdNormal.
-- If it uses named parameters,
-- those should be dependencies, so use `nonCenteredParameters'
simpleNonCentered :: ParameterEffs es
                  => SLS.NamedDeclSpec t
                  -> PT.TransformedParameterLocation
                  -> SLS.DeclSpec SLE.UExpr t
                  -> SLS.DensityWithArgs t
                  -> PT.Parameters qs
                  -> (SLE.ExprList qs -> SLE.UExpr t -> SLE.UExpr t)
                  -> Eff es (PT.Parameter t)
simpleNonCentered nds tpl rawDS (SLS.DensityWithArgs d tsE) =
  addNonCenteredParameter nds (exprListToParameters tsE) tpl rawDS d

addIndependentPriorP :: ParameterEffs es
                     => SLS.NamedDeclSpec t -> SLS.DensityWithArgs t -> Eff es (PT.Parameter t)
addIndependentPriorP nds (SLS.DensityWithArgs d dArgs) =
  addBuildParameter
  $ PT.UntransformedP nds [] (exprListToParameters dArgs)
  $ \argEs e -> SLC.addStmt $ SLS.sample e d argEs

addNonCenteredHierarchicalS :: ParameterEffs es
                            => SLS.NamedDeclSpec t
                            -> PT.TransformedParameterLocation
                            -> PT.Parameters ts
                            -> SLS.DensityWithArgs t
                            -> (SLE.ExprList ts -> SLE.UExpr t -> SLE.UExpr t)
                            -> Eff es (PT.Parameter t)
addNonCenteredHierarchicalS nds tpl ps (SLS.DensityWithArgs d dArgs) =
  addNonCenteredParameter nds (exprListToParameters dArgs) tpl (SLS.decl nds) d ps

addTransformedHP :: ParameterEffs es
                 => SLS.NamedDeclSpec t
                 -> PT.TransformedParameterLocation
                 -> Maybe (SLS.VarModifiers SLE.UExpr (SLT.ScalarType t))
                 -> SLS.DensityWithArgs t
                 -> (SLE.UExpr t -> SLE.UExpr t)
                 -> Eff es (PT.Parameter t)
addTransformedHP nds tpl rawCsM rawPrior fromRawF = do
  case SLS.decl nds of
    SLS.ScalarSpec st _ -> do
      let rawNDS = SLS.NamedDeclSpec (rawName $ SLS.declName nds) $ maybe (SLS.decl nds) (SLS.ScalarSpec st) rawCsM
      rawP <- addIndependentPriorP rawNDS rawPrior
      addBuildParameter $ simpleTransformedP nds [] (rawP :> TNil) tpl (\(e :> TNil) -> PT.DeclRHS $ fromRawF e)
    SLS.VectorSpec st l _ -> do
      let rawNDS = SLS.NamedDeclSpec (rawName $ SLS.declName nds) $ maybe (SLS.decl nds) (SLS.VectorSpec st l) rawCsM
      rawP <- addIndependentPriorP rawNDS rawPrior
      addBuildParameter $ simpleTransformedP nds [] (rawP :> TNil) tpl (\(e :> TNil) -> PT.DeclRHS $ fromRawF e) -- (ExprList qs -> DeclCode t)
    SLS.MatrixSpec st r c _ -> do
      let rawNDS = SLS.NamedDeclSpec (rawName $ SLS.declName nds) $ maybe (SLS.decl nds) (SLS.MatrixSpec st r c) rawCsM
      rawP <- addIndependentPriorP rawNDS rawPrior
      addBuildParameter $ simpleTransformedP nds [] (rawP :> TNil) tpl (\(e :> TNil) -> PT.DeclRHS $ fromRawF e) -- (ExprList qs -> DeclCode t)
    SLS.ArraySpec n arrDims ds -> do
      let rawNDS = SLS.NamedDeclSpec (rawName $ SLS.declName nds) $ maybe (SLS.decl nds) (\vms -> SLS.replaceDeclVMs vms (SLS.ArraySpec n arrDims ds)) rawCsM
      rawP <- addIndependentPriorP rawNDS rawPrior
      addBuildParameter $ simpleTransformedP nds [] (rawP :> TNil) tpl (\(e :> TNil) -> PT.DeclRHS $ fromRawF e) -- (ExprList qs -> DeclCode t)
    SLS.TupleSpec sts -> do -- this can't handle a change of constraints. Just removes them.
      let rawNDS = SLS.NamedDeclSpec (rawName $ SLS.declName nds) $ SLS.removeVMs $ SLS.TupleSpec sts
      rawP <- addIndependentPriorP rawNDS rawPrior
      addBuildParameter $ simpleTransformedP nds [] (rawP :> TNil) tpl (\(e :> TNil) -> PT.DeclRHS $ fromRawF e) -- (ExprList qs -> DeclCode t)

iidMatrixP :: ParameterEffs es
           => SLS.NamedDeclSpec SLT.EMat
           -> [PT.FunctionToDeclare]
           -> PT.Parameters qs
           -> SLF.Density SLT.ECVec qs
           -> Eff es (PT.Parameter SLT.EMat)
iidMatrixP nds ftd ps d = addBuildParameter $ iidMatrixBP nds ftd ps d


iidMatrixBP :: SLS.NamedDeclSpec SLT.EMat
            -> [PT.FunctionToDeclare]
            -> PT.Parameters qs
            -> SLF.Density SLT.ECVec qs
            -> PT.BuildParameter SLT.EMat
iidMatrixBP nds ftd ps d = PT.UntransformedP nds ftd ps
                           $ \qs m -> SLC.addStmt $ SLS.sample (SFC.to_vector m) d qs

-- this puts the prior on the raw parameters
withIIDRawMatrix :: ParameterEffs es
                 => SLS.NamedDeclSpec SLT.EMat
                 -> PT.TransformedParameterLocation
                 -> Maybe (SLS.VarModifiers SLE.UExpr SLT.EReal) -- constraints on raw
                 -> SLS.DensityWithArgs SLT.ECVec -- prior density on raw
                 -> PT.Parameters qs
                 -> (SLE.ExprList qs -> SLE.MatrixE -> SLE.MatrixE)
                 -> Eff es (PT.Parameter SLT.EMat)
withIIDRawMatrix nds tpl rawCsM dwa qs f = do
  let (SLS.NamedDeclSpec _ ds) = nds
  case ds of
     SLS.MatrixSpec _ rowsE colsE _ -> do
       let rawNDS = SLS.NamedDeclSpec (rawName $ SLS.declName nds) $ SLS.addVMs (fromMaybe SLS.NoModifiers rawCsM) $ SLS.matrixSpec rowsE colsE
       rawP <- SLS.withDWA (\d tl -> iidMatrixP rawNDS [] (exprListToParameters tl) d) dwa
       addBuildParameter $ simpleTransformedP nds [] (rawP :> qs) tpl (\(rmE :> qsE) -> PT.DeclRHS $ f qsE rmE)
     _ -> SBC.buildError "Parameters: withIIDRawMatrix called with non-matrix type!"

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
