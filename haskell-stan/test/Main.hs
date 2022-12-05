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
