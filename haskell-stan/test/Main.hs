{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
module Main where

import Models

import qualified KnitEnvironment as KE

import qualified Stan.ModelBuilder.TypedExpressions.DAG as DAG

import qualified Stan.ModelBuilder as S
import qualified Stan.ModelBuilder.TypedExpressions.Program as SP
import qualified Stan.ModelConfig as SC
import qualified Stan.ModelRunner as SMR
import qualified Stan.RScriptBuilder as SR
import qualified CmdStan as CS

import qualified Knit.Report as K
import qualified Knit.Effect.AtomicCache as K (cacheTime)

import qualified Data.Text as T
import qualified Control.Foldl as FL
import Control.Lens (view)

main :: IO ()
main = KE.knitToIO KE.defaultConfig $ do
  runMatchupsModel True 1
  runMatchupsModel False 2
  runMatchupsModel True 2
  runMatchupsModel False 1
  runMatchupsModel False 1
  runMatchupsModel False 2


runMatchupsModel :: forall st cd r.(K.KnitEffects r, KE.CacheEffects r) => Bool -> Int -> K.Sem r ()
runMatchupsModel clearCaches matchupsId = do
  let cacheKeyE = let k = "stan/test/result" in if clearCaches then Left k else Right k
      runnerInputNames = SC.RunnerInputNames
                         "haskell-stan/test/stan"
                         "normalSpreadDiff"
                         (Just $ SC.GQNames "normalSpreadDiffGQ" ("mu" <> show matchupsId))
                         "fb"
  fbResults_C <- fbResults @r
  fbMatchups_C <- fbMatchups matchupsId
  teams <- FL.fold (FL.premap (view favoriteName) FL.set) <$> K.ignoreCacheTime fbResults_C
  (dw, code) <- SMR.dataWranglerAndCode fbResults_C fbMatchups_C (groupBuilder teams) spreadDiffNormal
  (musCI, sigmaMuCI, sigmaCI, eScoreDiff) <- do
    K.ignoreCacheTimeM
    $ SMR.runModel' @KE.SerializerC @KE.CacheData
    cacheKeyE
    (Right runnerInputNames)
    dw
    code
    normalParamCIs
    (SMR.Both [])
    fbResults_C
    fbMatchups_C
  K.logLE K.Info $ "Matchups=" <> show matchupsId
  K.logLE K.Info $ "mus: " <> show musCI
  K.logLE K.Info $ "sigma_mu_fav: " <> show sigmaMuCI
  K.logLE K.Info $ "sigma: " <> show sigmaCI
  K.logLE K.Info $ "eScoreDiff: " <> show eScoreDiff

{-
-- This whole thing should be wrapped in the core for this very common variation.
dataWranglerAndCode :: forall md gq r. (K.KnitEffects r, Typeable md, Typeable gq)
                    => K.ActionWithCacheTime r md --F.Frame FB_Result
                    -> K.ActionWithCacheTime r gq --F.Frame FB_Matchup
                    -> S.StanGroupBuilderM md gq ()
                    -> S.StanBuilderM md gq ()
                    -> K.Sem r (SC.DataWrangler md gq S.DataSetGroupIntMaps (), SP.StanProgram)
dataWranglerAndCode modelData_C gqData_C gb sb = do
  modelDat <- K.ignoreCacheTime modelData_C
  gqDat <- K.ignoreCacheTime gqData_C
  let builderWithWrangler = do
        S.buildGroupIndexes
        sb
        modelJsonF <- S.buildModelJSONFromDataM
        gqJsonF <- S.buildGQJSONFromDataM
        modelIntMapsBuilder <- S.modelIntMapsBuilder
        gqIntMapsBuilder <- S.gqIntMapsBuilder
        let modelWrangle md = (modelIntMapsBuilder md, modelJsonF)
            gqWrangle gq = (gqIntMapsBuilder gq, gqJsonF)
            wrangler :: SC.DataWrangler md gq S.DataSetGroupIntMaps () =
              SC.Wrangle
              SC.TransientIndex
              modelWrangle
              (Just gqWrangle)
        return wrangler
      resE = DAG.runStanBuilderDAG modelDat gqDat gb builderWithWrangler
  K.knitEither $ fmap (\(bs, dw) -> (dw, S.program (S.code bs))) resE

runModel :: forall st cd md gq b c r.
            (SC.KnitStan st cd r
            , Typeable md
            , Typeable gq
            , st c
            )
         => Bool
         -> SC.RunnerInputNames
         -> SC.DataWrangler md gq b ()
         -> SP.StanProgram
         -> Text
         -> SC.ResultAction r md gq b () c
         -> K.ActionWithCacheTime r md
         -> K.ActionWithCacheTime r gq
         -> K.Sem r (K.ActionWithCacheTime r c)
runModel clearCaches rin dataWrangler stanProgram ppName resultAction modelData_C gqData_C =
  K.wrapPrefix "haskell-stan-test.runModel" $ do
  K.logLE K.Info
    $ "Running: model="
    <> SC.rinModel rin <> " using model data=" <> SC.rinData rin
    <> maybe "" (" and GQ data=" <>) (SC.gqDataName <$> SC.rinGQ rin)
  let outputLabel = SC.rinModel rin  <> "_" <> SC.rinData rin <> maybe "" ("_" <>) (SC.gqDataName <$> SC.rinGQ rin)
      stancConfig =
        (CS.makeDefaultStancConfig (toString $ SC.rinModelDir rin <> "/" <> SC.rinModel rin)) {CS.useOpenCL = False}
  stanConfig <-
    SC.setSigFigs 4
    . SC.noLogOfSummary
    <$> SMR.makeDefaultModelRunnerConfig @st @cd
    rin
    (Just (S.All, stanProgram))
    (SC.StanMCParameters 4 4 Nothing Nothing Nothing Nothing (Just 1))
    (Just stancConfig)
  let resultCacheKey = "stan/test/result/" <> outputLabel <> ".bin"
  when clearCaches $ do
    SMR.deleteStaleFiles @st @cd stanConfig [SMR.StaleData]
    K.clearIfPresent @Text @cd resultCacheKey
  modelDep <- SC.modelDependency SC.MRFull $ SC.mrcInputNames stanConfig
  K.logLE (K.Debug 1) $ "modelDep: " <> show (K.cacheTime modelDep)
  K.logLE (K.Debug 1) $ "modelDataDep: " <> show (K.cacheTime modelData_C)
  K.logLE (K.Debug 1) $ "gqDataDep: " <> show (K.cacheTime gqData_C)
  let dataModelDep = (,,) <$> modelDep <*> modelData_C <*> gqData_C
--      getResults s () inputAndIndex_C = return ()
      unwraps = if T.null ppName then [] else [SR.UnwrapNamed ppName ppName]
  K.retrieveOrMake @st @cd resultCacheKey dataModelDep $ \_ -> do
    K.logLE K.Diagnostic "Data or model newer then last cached result. (Re)-running..."
    SMR.runModel @st @cd
      stanConfig
      (SMR.Both unwraps)
      dataWrangler
      SC.UnCacheable
      resultAction
      ()
      modelData_C
      gqData_C
-}
