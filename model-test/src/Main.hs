{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators #-}
module Main where

import Models

import qualified KnitEnvironment as KE

import qualified Stan as S

import qualified Knit.Report as K

import qualified Control.Foldl as FL
import Control.Lens (view)

main :: IO ()
main = KE.knitToIO KE.defaultConfig $ do
  runMatchupsModel True 1
  runMatchupsModel False 2
  runMatchupsModel False 2
  runMatchupsModel False 1
  runMatchupsModel False 1
  runMatchupsModel False 2

runMatchupsModel :: forall st cd r.(K.KnitEffects r, KE.CacheEffects r) => Bool -> Int -> K.Sem r ()
runMatchupsModel clearCaches matchupsId = do
  let cacheKeyE = let k = "stan/model-test/result" in if clearCaches then Left k else Right k
      runnerInputNames = S.RunnerInputNames
                         "model-test/stan"
                         "normalSpreadDiff"
                         (Just $ S.GQNames "normalSpreadDiffGQ" ("mu" <> show matchupsId))
                         "fb"
  fbResults_C <- fbResults @r
  fbMatchups_C <- fbMatchups matchupsId
  teams <- FL.fold (FL.premap (view favoriteName) FL.set) <$> K.ignoreCacheTime fbResults_C
  (dw, code) <- S.dataWranglerAndCode fbResults_C fbMatchups_C (modelDataBuilder teams) (gqDataBuilder teams) spreadDiffNormal
  (musCI, sigmaMuCI, sigmaCI, eScoreDiff) <- do
    K.ignoreCacheTimeM
    $ S.runModel' @KE.SerializerC @KE.CacheData
    cacheKeyE
    (Right runnerInputNames)
    Nothing
    dw
    code
    normalParamCIs
    (S.Both [])
    fbResults_C
    fbMatchups_C
  K.logLE K.Info $ "Matchups=" <> show matchupsId
  K.logLE K.Info $ "mus: " <> show musCI
  K.logLE K.Info $ "sigma_mu_fav: " <> show sigmaMuCI
  K.logLE K.Info $ "sigma: " <> show sigmaCI
  K.logLE K.Info $ "eScoreDiff: " <> show eScoreDiff
