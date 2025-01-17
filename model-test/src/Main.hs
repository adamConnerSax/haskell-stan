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

import qualified Stan.Builder as SB
import qualified Stan.Runner as SR

{-
import qualified Stan.ModelBuilder.TypedExpressions.DAG as DAG

import qualified Stan.ModelBuilder as S
import qualified Stan.ModelBuilder.TypedExpressions.Program as SP
import qualified Stan.ModelConfig as SC
import qualified Stan.ModelRunner as SMR
import qualified Stan.RScriptBuilder as SR
import qualified CmdStan as CS
-}

import qualified Knit.Report as K
import qualified Knit.Effect.AtomicCache as K (cacheTime)

import qualified Data.Text as T
import qualified Control.Foldl as FL
import Control.Lens (view)

import Effectful
import Effectful.State.Static.Local as S

type TestEffs = [S.State Int, S.State Double]

runEffs :: Eff TestEffs a -> ((a, Int), Double)
runEffs = runPureEff . S.runState 0 . S.runState 0

runOuter :: Eff (S.State Int ': S.State Double ': es) a -> Eff (S.State Double ': es) (a, Int)
runOuter m = do
  (a, n) <- S.runState 0 m
  S.put $ realToFrac n
  pure (a, n)

runOuter2 :: Eff (S.State Int ': S.State Double ': es) a -> Eff es ((a, Int), Double)
runOuter2 m = do
  (a, n) <- S.runState 0 m
  S.put $ realToFrac n
  pure (a, n)

runEffs' :: Eff TestEffs a -> ((a, Int), Double)
runEffs' = runPureEff . S.runState 0 . runOuter


f :: Eff TestEffs ()
f = do
  S.modify @Int $ (+ 2)
  S.modify @Double $ (+ 3)
  pure ()

g :: Eff TestEffs ()
g = do
  S.modify @Double $ (+ 3)
  S.modify @Int $ (+ 2)
  pure ()

main :: IO ()
main = do
  putTextLn $ show $ runEffs f
  putTextLn $ show $ runEffs g
  putTextLn $ show $ runEffs' f
  putTextLn $ show $ runEffs' g




{-
main :: IO ()
main = KE.knitToIO KE.defaultConfig $ do
  runMatchupsModel True 1
  runMatchupsModel False 2
  runMatchupsModel True 2
  runMatchupsModel False 1
  runMatchupsModel False 1
  runMatchupsModel False 2
-}

runMatchupsModel :: forall st cd r.(K.KnitEffects r, KE.CacheEffects r) => Bool -> Int -> K.Sem r ()
runMatchupsModel clearCaches matchupsId = do
  let cacheKeyE = let k = "stan/test/result" in if clearCaches then Left k else Right k
      runnerInputNames = SR.RunnerInputNames
                         "haskell-stan/test/stan"
                         "normalSpreadDiff"
                         (Just $ SR.GQNames "normalSpreadDiffGQ" ("mu" <> show matchupsId))
                         "fb"
  fbResults_C <- fbResults @r
  fbMatchups_C <- fbMatchups matchupsId
  teams <- FL.fold (FL.premap (view favoriteName) FL.set) <$> K.ignoreCacheTime fbResults_C
  (dw, code) <- SR.dataWranglerAndCode fbResults_C fbMatchups_C (spreadDiffNormal teams)
  (musCI, sigmaMuCI, sigmaCI, eScoreDiff) <- do
    K.ignoreCacheTimeM
    $ SR.runModel' @KE.SerializerC @KE.CacheData
    cacheKeyE
    (Right runnerInputNames)
    Nothing
    dw
    code
    normalParamCIs
    (SR.Both [])
    fbResults_C
    fbMatchups_C
  K.logLE K.Info $ "Matchups=" <> show matchupsId
  K.logLE K.Info $ "mus: " <> show musCI
  K.logLE K.Info $ "sigma_mu_fav: " <> show sigmaMuCI
  K.logLE K.Info $ "sigma: " <> show sigmaCI
  K.logLE K.Info $ "eScoreDiff: " <> show eScoreDiff
