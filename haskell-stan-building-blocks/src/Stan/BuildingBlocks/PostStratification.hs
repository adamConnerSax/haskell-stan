{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use for_" #-}
{-# HLINT ignore "Use camelCase" #-}
module Stan.BuildingBlocks.PostStratification
  (
    module Stan.BuildingBlocks.PostStratification
  )
where

import Prelude hiding (sum, All)

import qualified Stan.Language as SL
import Stan.Language (TypedList(..))
import qualified Stan.Functions as SF
import Stan.Functions.Operators

import qualified Stan.Builder as SB

import Effectful (Eff)

ps_by_group :: SL.Function SL.ECVec [SL.EInt, SL.EInt, SL.EIndexArray, SL.ECVec, SL.ECVec]
ps_by_group = SL.simpleFunction "ps_by_group"

psByGroupFunction :: SB.StanFunctionsC es => Bool -> Eff es (SL.Function SL.ECVec [SL.EInt, SL.EInt, SL.EIndexArray, SL.ECVec, SL.ECVec])
psByGroupFunction wgtsAreData = do
  let wgtsArg = if wgtsAreData then SL.DataArg "wgts" else SL.Arg "wgts"
  SB.addFunctionOnce ps_by_group (SL.DataArg "Nps" :> SL.DataArg "Ngrp" :> SL.DataArg "grpPSIndex" :> wgtsArg :> SL.Arg "probs" :> TNil)
    $ \(nPS :> nGrp :> grpPSIndex :> wgts :> probs :> TNil) -> SL.cwStmt $ do
    let vds = SL.vectorSpec nGrp
    sumByGroup <- SL.declareRHSW "SumByGroup" vds $ SF.rep_vector (SL.realE 0) nGrp --zeroVectorE nGrp
    sumWgts <- SL.declareRHSW "SumWgts" vds $  SF.rep_vector (SL.realE 0) nGrp --zeroVectorE nGrp
    SL.addStmt $ SL.for "k" (SL.SpecificNumbered (SL.intE 1) nPS)
      $ \k ->
          let atk = SL.slice0 k
              indexByPS = SL.indexE SL.s0 grpPSIndex
          in SL.grouped [atk (indexByPS sumByGroup) SL.+= (atk wgts |*| atk probs)
                        , atk (indexByPS sumWgts) SL.+= atk wgts
                        ]
    -- we do the division in a loop so we can avoid the divide by zero of empty groups
    SL.addStmt $ SL.for "l" (SL.SpecificNumbered (SL.intE 1) nGrp)
      $ \l ->
          let atl = SL.slice0 l
              sbgl = atl sumByGroup
              swl = atl sumWgts
              z = SL.realE 0
          in sbgl SL.|=| SL.condE (swl |>| z) (sbgl |/| swl) z

--    SL.addStmt $ sumByGroup `elDivEq` sumWgts
    return sumByGroup

{-
psByGroupFunction :: SB.StanBuilderM md gq ()
psByGroupFunction = SB.addFunctionsOnce "psByGroup"
                      $ SB.declareStanFunction "vector psByGroup(int Nps, int Ngrp, array[] int grpPSIndex, vector wgts, vector probs)" $ do
  SB.addStanLine "vector[Ngrp] SumByGroup = rep_vector(0, Ngrp)"
  SB.addStanLine "vector[Ngrp] SumWgts = rep_vector(0, Ngrp)"
  SB.addLine "for (k in 1:Nps) {\n"
  SB.addStanLine "  SumByGroup[grpPSIndex[k]] += wgts[k] * probs[grpPSIndex[k]]"
  SB.addStanLine "  SumWgts[grpPSIndex[k]] += wgts[k]"
  SB.addLine "}\n"
  SB.addStanLine "SumByGroup ./= SumWgts"
  SB.addStanLine "return SumByGroup"
-}

postStratifiedParameterF :: SB.StanFunctionsC es
                         => Bool
                         -> SL.StanBlock
                         -> Maybe SL.VarName
                         -> SB.RowTypeTag r -- data set to post-stratify
                         -> SB.GroupTypeTag k -- group by
                         -> SL.UExpr SL.EIndexArray -- PS Index for group
                         -> SL.MaybeCW SL.VectorE -- PS weight
                         -> SL.CodeWriter SL.VectorE --  code for expression of parameters to post-stratify. Should be indexed by PS data
                         -> Maybe (SB.RowTypeTag r', SL.UExpr SL.EIndexArray) -- re-index?
                         -> Eff es (SL.UExpr SL.ECVec)
postStratifiedParameterF prof block varNameM rtt gtt grpIndex wgtsMCW pCW reIndexRttM = do
  _ <- psByGroupFunction
       $ case wgtsMCW of
           SL.NoCW _ -> True
           SL.NeedsCW _ -> False
  let dsName = SB.dataSetName rtt
      gName = SB.taggedGroupName gtt
      dsSizeE = SL.namedE (SB.dataSetSizeName rtt) SL.SInt
      grpSizeE = SL.namedE (SB.groupSizeName gtt) SL.SInt
      psDataByGroupName = dsName <> "_By_" <> gName
--      indexName = SB.dataSetName rtt <> "_" <> SB.taggedGroupName gtt
      varName = case reIndexRttM of
        Nothing -> fromMaybe psDataByGroupName varNameM
        Just (reIndexRtt, _) -> fromMaybe (dsName <> "_By_" <> SB.dataSetName reIndexRtt) varNameM
      grpVecDS =  SL.vectorSpec grpSizeE --SB.StanVector $ SB.NamedDim gName
--      psVecDS =  SL.vectorSpec dsSizeE [] --SB.StanVector $ SB.NamedDim dsName
      scopeF :: SL.UStmt -> SL.UStmt
      scopeF stmt = if prof then SL.profile varName stmt else SL.scoped stmt
  SB.inBlock block $ case reIndexRttM of
    Nothing -> do
      probV <- SB.addFromCodeWriter $ SL.declareW varName grpVecDS
      SB.addStmtToCode $ scopeF $ SL.cwStmt_ $ do
        pV <- pCW
        wgtsV <- SL.asCW wgtsMCW
        SL.addStmt $ probV `SL.assign` SL.functionE ps_by_group (dsSizeE :>  grpSizeE :> grpIndex :> wgtsV :> pV :> TNil)
      pure probV
    Just (reIndexRtt, reIndex') -> do
      riProb <-  SB.addFromCodeWriter
                 $ SL.declareW varName $ SL.vectorSpec (SL.namedE (SB.dataSetSizeName reIndexRtt) SL.SInt) --(SB.StanVector $ SB.NamedDim reIndexKey) ""
      SB.addStmtToCode $ scopeF $ SL.cwStmt_ $ do
        pV <- pCW
        wgtsV <- SL.asCW wgtsMCW
        gProb <- SL.declareRHSW psDataByGroupName grpVecDS $ SL.functionE ps_by_group (dsSizeE :>  grpSizeE :> grpIndex :> wgtsV :> pV :> TNil)
        SL.addStmt $ riProb `SL.assign` SL.indexE SL.s0 reIndex' gProb
      pure riProb

{-
postStratifiedParameter :: (Typeable md, Typeable gq)
                        => Bool
                        -> Maybe Text
                        -> SB.RowTypeTag r -- data set to post-stratify
                        -> SB.GroupTypeTag k -- group by
                        -> SB.StanExpr -- weight
                        -> SB.StanExpr -- expression of parameters to post-stratify
                        -> Maybe (SB.RowTypeTag r') -- re-index?
                        -> SB.StanBuilderM md gq SB.StanVar
postStratifiedParameter prof varNameM rtt gtt wgtE pE reIndexRttM = do
  let dsName = SB.dataSetName rtt
      gName = SB.taggedGroupName gtt
      psDataByGroupName = dsName <> "_By_" <> gName
      varName = case reIndexRttM of
        Nothing -> fromMaybe psDataByGroupName varNameM
        Just reIndexRtt -> fromMaybe (SB.dataSetName rtt <> "_By_" <> SB.dataSetName reIndexRtt) varNameM
      profF :: SB.StanBuilderM md gq a -> SB.StanBuilderM md gq a
      profF = if prof then SB.profile varName else SB.bracketed 2
      zeroVec indexKey varName = SB.stanDeclareRHS
                                 varName
                                 (SB.StanVector $ SB.NamedDim indexKey)
                                 ""
                                 (zeroVectorE indexKey)
      psLoops pV wV = do
        SB.stanForLoopB "k" Nothing dsName
          $ SB.addExprLines "postStratifiedParameter"
          [SB.var pV `SB.plusEq` (SB.paren wgtE `SB.times` SB.paren pE)
          , SB.var wV `SB.plusEq` SB.paren wgtE]
        SB.addExprLine "postStratifiedParameter" $ SB.vectorizedOne gName $ SB.binOp "./=" (SB.var pV) (SB.var wV)
  SB.inBlock SB.SBTransformedParameters $ case reIndexRttM of
    Nothing -> do
      gProb <- zeroVec gName varName
      gWeight <- zeroVec gName (varName <> "_wgts")
      profF $ SB.useDataSetForBindings rtt $ do
        psLoops gProb gWeight
        return gProb
    Just reIndexRtt -> do
      let reIndexKey = SB.dataSetName reIndexRtt
      riProb <-  SB.stanDeclare varName(SB.StanVector $ SB.NamedDim reIndexKey) ""
      profF $ SB.useDataSetForBindings rtt $ do
        gProb <- zeroVec gName psDataByGroupName
        gWeight <- zeroVec gName (psDataByGroupName <> "_wgts")
        psLoops gProb gWeight
        SB.useDataSetForBindings reIndexRtt
          $ SB.addExprLine "postStratifiedParameter"
          $ SB.vectorizedOne reIndexKey
          $ SB.var riProb `SB.eq` SB.var gProb
      return riProb
-}
