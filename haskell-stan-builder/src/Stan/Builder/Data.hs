{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Stan.Builder.Data
  (
    module Stan.Builder.Data
  )
where

import qualified Stan.Builder.Core as SBC
import qualified Stan.Language as SL

import Prelude hiding (All)
import qualified Data.Dependent.HashMap as DHash

import Effectful ((:>), Eff)
import qualified Effectful.State.Static.Local as EffS
import qualified Effectful.Fail as EffF

addData :: forall es r i . (Typeable r, Typeable i, EffF.Fail :> es, EffS.State (SBC.RowInfoMakers i) :> es)
        => Text -> SBC.InputDataType i  -> SBC.ToFoldable (SBC.DataSource i) r -> Eff es (SBC.RowTypeTag i r)
addData name idt tf = do
  rowInfoMakers <- EffS.get @(SBC.RowInfoMakers i)
  let rtt = SBC.RowTypeTag idt name
  case DHash.lookup rtt rowInfoMakers of
    Just _ -> SBC.buildError $ "Attempt to add data of matching type and name (\"" <> name <> "\" to model-data."
    Nothing -> do
      let newRowInfoMakers = DHash.insert rtt (SBC.GroupIndexAndIntMapMakers tf (SBC.GroupIndexMakers DHash.empty) (SBC.GroupIntMapBuilders DHash.empty)) rowInfoMakers
      EffS.put newRowInfoMakers
      pure rtt

dataSetSizeName :: SBC.RowTypeTag i r -> Text
dataSetSizeName rtt = "N_" <> SBC.dataSetName rtt

dataSetSizeE :: SBC.RowTypeTag i r -> SL.IntE
dataSetSizeE rtt = SL.namedSizeE $ "N_" <> SBC.dataSetName rtt
