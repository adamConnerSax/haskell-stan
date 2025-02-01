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

import Effectful (Eff)
import qualified Effectful.State.Static.Local as EffS

addData :: forall r i d es  . (Typeable r, SBC.StanDataBuildersC i d es)
        => Text -> SBC.InputDataType i d  -> SBC.ToFoldable d r -> Eff es (SBC.RowTypeTag r)
addData name _idt tf = do
  rowInfoMakers <- EffS.get @(SBC.RowInfoMakers i d)
  let rtt = SBC.RowTypeTag name
  case DHash.lookup rtt $ SBC.unRowInfoMakers rowInfoMakers of
    Just _ -> SBC.buildError $ "Attempt to add data of matching type and name (\"" <> name <> "\" to model-data."
    Nothing -> do
      let newRowInfoMakers = SBC.RowInfoMakers
                             $ DHash.insert rtt (SBC.GroupIndexAndIntMapMakers tf (SBC.GroupIndexMakers DHash.empty) (SBC.GroupIntMapBuilders DHash.empty))
                             $ SBC.unRowInfoMakers rowInfoMakers
      EffS.put @(SBC.RowInfoMakers i d) newRowInfoMakers
      pure rtt

dataSetSizeName :: SBC.RowTypeTag r -> Text
dataSetSizeName rtt = "N_" <> SBC.dataSetName rtt

dataSetSizeE :: SBC.RowTypeTag r -> SL.IntE
dataSetSizeE rtt = SL.namedSizeE $ "N_" <> SBC.dataSetName rtt
