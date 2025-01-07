{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Stan.Builder.JSON
  (
    module Stan.Builder.JSON
  )
where

import qualified Stan.Builder.JSON.JSONUtils as SBJU
import qualified Stan.Builder.Core as SBC
import qualified Stan.Builder.Build as SBB

import qualified Stan.Language.Types as SLT
import qualified Stan.Language.Program as SLP
import qualified Stan.Language.Format as SLF
import qualified Stan.Language.ASTContext as SLA
import qualified Stan.Language.Expression as SLE
import qualified Stan.Language.Expressions as SLE
import qualified Stan.Language.Statement as SLS
import qualified Stan.Language.Statements as SLS
import qualified Stan.Language.CodeWriter as SLC
import qualified Stan.Builder.ParameterTypes as SBPT

import Prelude hiding (All)
import qualified Control.Foldl as Foldl
import qualified Data.Aeson as Aeson
import qualified Data.Dependent.HashMap as DHash
import qualified Data.GADT.Compare as GADT
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Some as Some
import qualified Data.Text as T
import qualified Data.Hashable as Hashable
import qualified Type.Reflection as Reflection
import qualified Data.GADT.Show as GADT
import qualified Data.Dependent.Sum as DSum
import qualified Data.Dependent.Map as DM
import qualified Data.Vector.Unboxed as VU

import qualified Effectful as Eff
import Effectful ((:>), Eff)
import qualified Effectful.State.Static.Local as EffS
import qualified Effectful.Fail as EffF

type AddJsonC r es = (EffF.Fail :> es, EffS.State SBC.StanCode :> es, EffS.State (SBC.RowInfos (SBC.DataSource r)) :> es)

data MatrixRowFromData r = MatrixRowFromData { rowName :: SLT.VarName, colIndexM :: Maybe SLT.VarName, rowLength :: Int, rowVec :: r -> VU.Vector Double }

add2dMatrixJson :: AddJsonC r es
                => SBC.RowTypeTag r
                -> MatrixRowFromData r
                -> SLS.VarModifiers SLE.UExpr SLT.EReal
                -> SLE.IntE
                -> SLE.IntE
                -> Eff es SLE.MatrixE
add2dMatrixJson rtt mrfd@(MatrixRowFromData tName _ cols vecF) cs rowsE colsE = do
  let dsName = SBC.dataSetName rtt
      wdName = tName <> underscoredIf dsName
      ndsF rowsE = SLS.NamedDeclSpec wdName $ SLS.addVMs cs $ SLS.matrixSpec rowsE colsE
      idt = SBC.inputDataType rtt
  addColumnJson rtt ndsF rowsE vecF

mrfdColumnsName :: MatrixRowFromData r -> SLT.VarName
mrfdColumnsName mrfd = "K_" <> fromMaybe mrfd.rowName mrfd.colIndexM

addColumnMJson :: (Aeson.ToJSON x, AddJsonC r es)
               => SBC.RowTypeTag r
               -> (SLE.IntE -> SLS.NamedDeclSpec t)
               -> SLE.IntE
               -> (r -> Either Text x)
               -> Eff es (SLE.UExpr t)
addColumnMJson rtt ndsF lengthE toMX = do
  let nds = ndsF lengthE
  addJson rtt nds (SBJU.valueToPairF (SLS.declName nds) $ SBJU.jsonArrayEF toMX)

addColumnJson :: (Aeson.ToJSON x, AddJsonC r es)
              => SBC.RowTypeTag r
              -> (SLE.IntE -> SLS.NamedDeclSpec t)
              -> SLE.IntE
              -> (r -> x)
              -> Eff es (SLE.UExpr t)
addColumnJson rtt ndsF lengthE toX = do
  let nds = ndsF lengthE
  addJson rtt nds (SBJU.valueToPairF (SLS.declName nds) $ SBJU.jsonArrayF toX)


addLengthJson :: AddJsonC r es
              => SBC.RowTypeTag r
              -> SLT.VarName
              -> Eff es SLE.IntE
addLengthJson rtt tName = addJson rtt (SLS.NamedDeclSpec tName ds) (SBJU.namedF tName Foldl.length)
  where
    ds = SLS.addVMs (SLS.Modifiers [SLS.lowerM $ SLE.intE 1]) SLS.intSpec

addFixedIntJson :: (EffF.Fail :> es, EffS.State SBC.ConstJsonFolds :> es, EffS.State SBC.StanCode :> es)
                => SBC.InputDataType -> Text -> Maybe Int -> Int -> Eff es SLE.IntE
addFixedIntJson idt tName mLower n = do
  let ds = flip SLS.addVMs SLS.intSpec $ maybe SLS.NoModifiers (SLS.Modifiers . pure . SLS.lowerM . SLE.intE) mLower
      codeBlock = if idt == SBC.ModelData then SLP.SBData else SLP.SBDataGQ
  ie <- SBB.inBlock codeBlock $ SBB.addFromCodeWriter $ SLC.declareW tName ds
  addConstJson idt (SBC.JSONSeriesFold $ SBJU.constDataF tName n)
  return ie -- $ TE.namedE tName TE.SInt


addConstJson :: (EffS.State SBC.ConstJsonFolds :> es) => SBC.InputDataType -> SBC.JSONSeriesFold () -> Eff es ()
addConstJson idt jf = do
  (SBC.ConstJsonFolds mf gqf) <- EffS.get
  case idt of
    SBC.ModelData -> EffS.put $ SBC.ConstJsonFolds (mf <> jf) gqf
    SBC.GQData -> EffS.put $ SBC.ConstJsonFolds mf (gqf <> jf)


addJson :: forall t r es . AddJsonC r es
        => SBC.RowTypeTag r
        -> SLS.NamedDeclSpec t
        -> SBJU.StanJSONF r Aeson.Series
        -> Eff es (SLE.UExpr t)
addJson rtt nds fld = do
  let codeBlock = if SBC.inputDataType rtt == SBC.ModelData then SLP.SBData else SLP.SBDataGQ
  ve <- SBB.inBlock codeBlock $ SBB.addFromCodeWriter $ SLC.declareNW nds
  let addFold :: SBC.RowInfos x -> Eff es (SBC.RowInfos x)
      addFold rowInfos = case addFoldToDBuilder rtt fld rowInfos of
        Nothing -> SBC.buildError $ "Attempt to add Json to an uninitialized dataset (" <> SBC.dataSetName rtt <> ")"
        Just x -> return x
  oldRowInfos <- EffS.get @(SBC.RowInfos (SBC.DataSource r))
  newRowInfos <- addFold oldRowInfos
  EffS.put newRowInfos
  return ve

addFoldToDBuilder :: forall d r.
                     SBC.RowTypeTag r
                  -> SBJU.StanJSONF r Aeson.Series
                  -> SBC.RowInfos d
                  -> Maybe (SBC.RowInfos d)
addFoldToDBuilder rtt fld ris =
  case DHash.lookup rtt ris of
    Nothing -> Nothing --DHash.insert rtt (RowInfo (JSONSeriesFold fld) (const Nothing)) rbm
    Just (SBC.RowInfo x y z (SBC.JSONSeriesFold fld'))
      -> Just $ DHash.insert rtt (SBC.RowInfo x y z (SBC.JSONSeriesFold $ fld' <> fld)) ris

underscoredIf :: Text -> Text
underscoredIf t = if T.null t then "" else "_" <> t
