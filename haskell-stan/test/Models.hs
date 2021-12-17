{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications     #-}

module Models where

import qualified KnitEnvironment as KE

import qualified Stan.ModelBuilder as S
import qualified Stan.ModelBuilder.BuildingBlocks as SBB
import qualified Stan.ModelBuilder.Expressions as SE
import qualified Stan.ModelBuilder.Distributions as SD
import qualified Stan.ModelBuilder.GroupModel as SGM
import qualified Stan.ModelConfig as SC
import qualified Stan.Parameters as SP
import qualified CmdStan as CS

import qualified Frames as F hiding (tableTypes)
import qualified Frames.Streamly.TH as F
import qualified Frames.Streamly.LoadInCore as F
import qualified Frames.Streamly.Streaming.Class as FSC
import qualified Frames.Streamly.Streaming.Streamly as FS

import qualified Knit.Report as K

import qualified Data.IntMap as IM
import qualified Data.Vector as Vec
import Control.Lens ((^.), view)

-- remove "haskell-stan" from these paths if this becomes it's own project
F.tableTypes "FB_Result" ("haskell-stan/test/data/football.csv")
F.tableTypes "FB_Matchup" ("haskell-stan/test/data/matchups1.csv")


fbResults :: forall r.(K.KnitEffects r, KE.CacheEffects r) => K.Sem r (K.ActionWithCacheTime r (F.Frame FB_Result))
fbResults = do
  let cacheKey :: Text = "data/fbResults.bin"
      fp = "haskell-stan/test/data/football.csv"
  fileDep <- K.fileDependency fp
  sf <- K.retrieveOrMake @KE.SerializerC @KE.CacheData cacheKey fileDep
        $ const
        $ fmap KE.fromFrame
        $ K.liftKnit -- we have to run this in IO since K.Sem r does not support Monad Control
        $ FSC.runSafe @F.DefaultStream
        $ F.loadInCore @F.DefaultStream @IO fB_ResultParser fp Just
  return $ fmap KE.toFrame sf

fbMatchups :: forall r.(K.KnitEffects r, KE.CacheEffects r) => Int -> K.Sem r (K.ActionWithCacheTime r (F.Frame FB_Matchup))
fbMatchups n = do
  let cacheKey :: Text = "data/fbMatchups" <> show n <> ".bin"
      fp = "haskell-stan/test/data/matchups" <> show n <> ".csv"
  fileDep <- K.fileDependency fp
  sf <- K.retrieveOrMake @KE.SerializerC @KE.CacheData cacheKey fileDep
        $ const
        $ fmap KE.fromFrame
        $ K.liftKnit -- we have to run this in IO since K.Sem r does not support Monad Control
        $ FSC.runSafe @F.DefaultStream
        $ F.loadInCore @F.DefaultStream @IO fB_MatchupParser fp Just
  return $ fmap KE.toFrame sf


data HomeField = FavoriteField | UnderdogField deriving (Show, Eq, Ord, Enum, Bounded)

homeField :: FB_Result -> HomeField
homeField r = if r ^. home then FavoriteField else UnderdogField

homeFieldG :: S.GroupTypeTag HomeField = S.GroupTypeTag "HomeField"

favoriteG :: S.GroupTypeTag Text = S.GroupTypeTag "Favorite"

underdogG :: S.GroupTypeTag Text = S.GroupTypeTag "Underdog"

-- spread :: F.Record FB_Results -> Double
-- spread = F.rgetField @Spread

scoreDiff :: FB_Result -> Double
scoreDiff r = realToFrac (r ^. favorite) - realToFrac (r ^. underdog)

spreadDiff :: FB_Result -> Double
spreadDiff r = r ^. spread - scoreDiff r

groupBuilder :: Foldable f => f Text -> S.StanGroupBuilderM (F.Frame FB_Result, F.Frame FB_Matchup) ()
groupBuilder teams = do
  resultsData <- S.addDataSetToGroupBuilder "Results" (S.ToFoldable fst)
  S.addGroupIndexForDataSet homeFieldG resultsData $ S.makeIndexFromEnum homeField
  S.addGroupIndexForDataSet favoriteG resultsData $ S.makeIndexFromFoldable show (F.rgetField @FavoriteName) teams
  S.addGroupIntMapForDataSet favoriteG resultsData $ S.dataToIntMapFromFoldable (F.rgetField @FavoriteName) teams
  matchupData <- S.addDataSetToGroupBuilder "Matchups" (S.ToFoldable snd)
  S.addGroupIndexForDataSet favoriteG matchupData $ S.makeIndexFromFoldable show (F.rgetField @FavoriteName) teams
--  S.addGroupIndexForDataSet underdogG resultsData $ S.makeIndexFromFoldable show (F.rgetField @UnderdogName) teams
  return ()

spreadDiffNormal :: S.StanBuilderM () (F.Frame FB_Result, F.Frame FB_Matchup) ()
spreadDiffNormal = do
  resultsData <- S.dataSetTag @FB_Result "Results"
  S.setDataSetForBindings resultsData
  spreadDiffV <- SBB.addRealData resultsData "diff" Nothing Nothing spreadDiff
  let normal m s = SD.normal (Just $ SE.scalar $ show m) $ SE.scalar $ show s
      muModel = SGM.hierarchicalCenteredFixedMeanNormal 0 "sigma_mu_fav" (normal 0 3) SGM.STZNone
  mu_favV <- SGM.groupModel (S.StanVar "mu_fav" $ S.StanVector $ S.NamedDim "Favorite") muModel
  sigmaV <- S.inBlock S.SBParameters $ S.stanDeclare "sigma" S.StanReal ""
  S.inBlock S.SBModel $ S.addExprLines "priors"
    [
      SE.var sigmaV `SE.vectorSample` normal 13 5
    ]
  SBB.sampleDistV resultsData SD.normalDist (S.var mu_favV, S.var sigmaV) spreadDiffV
  S.inBlock S.SBGeneratedQuantities $ do
    matchups <- S.dataSetTag @FB_Matchup "Matchups"
    S.useDataSetForBindings matchups $ do
      S.stanDeclareRHS "eScoreDiff" (S.StanVector $ S.NamedDim "Matchups") ""
        $ SE.vectorizedOne "Matchups"
        $ SD.familyExp SD.normalDist (S.var mu_favV, S.var sigmaV)
      return ()

-- the getParameter function feels like an incantation.  Need to simplify.
type ModelReturn = ([(Text, [Double])],[Double], [Double])
normalParamCIs :: K.KnitEffects r => SC.ResultAction r d S.DataSetGroupIntMaps () ModelReturn
normalParamCIs = SC.UseSummary f where
  f summary _ dataAndIndexes_C = do
    indexesE <- K.ignoreCacheTime $ fmap snd dataAndIndexes_C
    teamResultIM <- K.knitEither $ do
      groupIndexes <- indexesE
      S.getGroupIndex (S.RowTypeTag @FB_Result "Results") favoriteG groupIndexes
    let teamList = fmap snd $ IM.toAscList teamResultIM
    let getScalar n = K.knitEither $ SP.getScalar . fmap CS.percents <$> SP.parseScalar n (CS.paramStats summary)
        getVector n = K.knitEither $ SP.getVector . fmap CS.percents <$> SP.parse1D n (CS.paramStats summary)
        addTeams = fmap (zip teamList . Vec.toList)
    (,,) <$> addTeams (getVector "mu_fav") <*> getScalar "sigma_mu_fav" <*> getScalar "sigma"
