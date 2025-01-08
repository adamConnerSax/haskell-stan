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
--import qualified Stan.Builder.JSON as SBJ
--import qualified Stan.Language.Expressions as SLE

import Prelude hiding (All)
--import qualified Control.Foldl as Foldl
import qualified Data.Dependent.HashMap as DHash
--import qualified Data.IntMap.Strict as IntMap
--import qualified Data.Map.Strict as Map
--import qualified Data.Set as Set

import Effectful ((:>), Eff)
import qualified Effectful.State.Static.Local as EffS
import qualified Effectful.Fail as EffF

addData :: forall es r i . (Typeable r, EffF.Fail :> es, EffS.State (SBC.RowInfoMakers (SBC.DataSource r)) :> es, SBC.DataSource r ~ SBC.SourceType i)
        => SBC.DataSource r -> Text -> SBC.InputDataType i  -> SBC.ToFoldable (SBC.DataSource r) r -> Eff es (SBC.RowTypeTag r)
addData _d name idt tf = do
  rowInfoMakers <- EffS.get @(SBC.RowInfoMakers (SBC.DataSource r))
  let rtt = SBC.RowTypeTag (SBC.inputDataT idt) name
  case DHash.lookup rtt rowInfoMakers of
    Just _ -> SBC.buildError $ "Attempt to add data of matching type and name (\"" <> name <> "\" to model-data."
    Nothing -> do
      let newRowInfoMakers = DHash.insert rtt (SBC.GroupIndexAndIntMapMakers tf (SBC.GroupIndexMakers DHash.empty) (SBC.GroupIntMapBuilders DHash.empty)) rowInfoMakers
      EffS.put newRowInfoMakers
      pure rtt
