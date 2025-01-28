{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies     #-}

module Models where

import qualified KnitEnvironment as KE

import qualified Stan as S
import Stan (TypedList(..))
import Stan.Operators

{-import Stan.Language (TypedList(..))
import qualified Stan.Functions as SF
import Stan.Functions.Operators
import qualified Stan.Builder as SB
import qualified Stan.BuildingBlocks as SBB
import qualified Stan.Runner as SR
-}
import qualified CmdStan as CS

import qualified Frames as F hiding (tableTypes)
import qualified Frames.Streamly.TH as F
import qualified Frames.Streamly.LoadInCore as F
import qualified Frames.Streamly.Streaming.Class as FSC
import qualified Frames.Streamly.Streaming.Streamly as FS

import qualified Knit.Report as K
import Effectful (Eff)
import qualified Data.IntMap as IM
import qualified Data.Vector as Vec
import qualified Control.Foldl as FL
import Control.Lens ((^.), view)

import ModelPaths

F.tableTypes "FB_Result" (dataDir <> "model-test/data/football.csv")
F.tableTypes "FB_Matchup" (dataDir <> "model-test/data/matchups1.csv")

-- these type family instances are required for the stan builders
type ModelData = F.Frame FB_Result
type GQData = F.Frame FB_Matchup

fbResults :: forall r.(K.KnitEffects r, KE.CacheEffects r) => K.Sem r (K.ActionWithCacheTime r (F.Frame FB_Result))
fbResults = do
  let cacheKey :: Text = "data/fbResults.bin"
      fp = dataDir <> "model-test/data/football.csv"
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
      fp = dataDir <> "model-test/data/matchups" <> show n <> ".csv"
  fileDep <- K.fileDependency fp
  sf <- K.retrieveOrMake @KE.SerializerC @KE.CacheData cacheKey fileDep
        $ const
        $ fmap KE.fromFrame
        $ K.liftKnit -- we have to run this in IO since K.Sem r does not support Monad Control
        $ FSC.runSafe @F.DefaultStream
        $ F.loadInCore @F.DefaultStream @IO fB_MatchupParser fp Just
  return $ fmap KE.toFrame sf


data HomeField = FavoriteField | UnderdogField deriving (Show, Eq, Ord, Enum, Bounded)

data ModelDataPkg =
  ModelDataPkg { resultsT :: S.RowTypeTag ModelData FB_Result
               , homeFieldG :: S.GroupTypeTag HomeField
               , favoriteG :: S.GroupTypeTag Text
               , favoriteSize :: S.IntE
               , underDogG :: S.GroupTypeTag Text
               }

data GQDataPkg = GQDataPkg { matchupsT :: S.RowTypeTag GQData FB_Matchup }

homeField :: FB_Result -> HomeField
homeField r = if r ^. home then FavoriteField else UnderdogField

scoreDiff :: FB_Result -> Double
scoreDiff r = realToFrac (r ^. favorite) - realToFrac (r ^. underdog)

spreadDiff :: FB_Result -> Double
spreadDiff r = r ^. spread - scoreDiff r

modelDataBuilder :: Foldable f => f Text -> S.StanDataBuilderEff S.ModelDataT ModelData ModelDataPkg
modelDataBuilder teams = do
  resultsT <- S.addData "Results" S.ModelDataT (S.ToFoldable id)
  (homeFieldG, _) <- S.addGroup @HomeField @S.ModelDataT @ModelData "HomeField" 2
  (favoriteG, favoriteSize) <- S.addGroup @Text @S.ModelDataT @ModelData "Favorite" $ FL.fold FL.length teams
  (underdogG, _) <- S.addGroup @Text @S.ModelDataT @ModelData "Underdog" $ FL.fold FL.length teams
  S.addGroupIndexForData homeFieldG resultsT $ S.makeIndexFromEnum homeField
  S.addGroupIndexForData favoriteG resultsT $ S.makeIndexFromFoldable show (F.rgetField @FavoriteName) teams
  S.addGroupIntMapForData favoriteG resultsT $ S.dataToIntMapFromFoldable (F.rgetField @FavoriteName) teams
  pure $ ModelDataPkg resultsT homeFieldG favoriteG favoriteSize underdogG

gqDataBuilder :: Foldable f => f Text -> ModelDataPkg -> S.StanDataBuilderEff S.GQDataT GQData GQDataPkg
gqDataBuilder teams mdp = do
   matchupDataT <- S.addData "Matchups" S.GQDataT (S.ToFoldable id)
   S.addGroupIndexForData (favoriteG mdp) matchupDataT $ S.makeIndexFromFoldable show (F.rgetField @FavoriteName) teams
   S.addGroupIntMapForData (favoriteG mdp) matchupDataT $ S.dataToIntMapFromFoldable (F.rgetField @FavoriteName) teams
   pure $ GQDataPkg matchupDataT

spreadDiffNormal :: ModelDataPkg -> GQDataPkg -> S.StanModelBuilderEff ModelData GQData ()
spreadDiffNormal (ModelDataPkg resultsT homeFieldG favoriteG favoriteSize underDogG) (GQDataPkg matchupT) = do
  spreadDiffE <- S.addRealData @S.ModelDataT resultsT "diff" Nothing Nothing spreadDiff

  -- parameters
  sigmaMuP <- S.simpleParameter
              (S.NamedDeclSpec "sigma_mu_fav" $ S.addVMs (S.Modifiers [S.lowerM $ S.realE 0]) S.realSpec)
              (S.given (S.realE 0) :> S.given (S.realE 3) :> TNil)
              S.normal
  sigmaP <- S.simpleParameter
         (S.NamedDeclSpec "sigma" $ S.addVMs (S.Modifiers [S.lowerM $ S.realE 0]) S.realSpec)
         (S.given (S.realE 13) :> S.given (S.realE 15) :> TNil)
         $ S.normal
  muVP <- S.simpleParameter
          (S.NamedDeclSpec "mu_fav" $ S.vectorSpec favoriteSize)
          (S.given (S.realE 0) :> sigmaMuP :> TNil)
          $ S.normalS

  -- get expressions for the parameters we need to model the data
  let (sigmaE :> muVecE :> TNil) = S.parametersAsExprs (sigmaP :> muVP :> TNil)

  -- helper functions
  let toVec rtt x = S.rep_vector x (S.dataSetSizeE rtt)
      indexed rtt gtt = S.indexE S.s0 (S.dataByGroupIndexE rtt gtt)

  -- model (non-parameter part)
  S.inBlock S.SBModel
    $ S.addStmtToCode
    $ S.familySample S.normalDist spreadDiffE (indexed resultsT favoriteG muVecE :> toVec resultsT sigmaE :> TNil)

  -- generated quantities, in this case a prediction
  S.inBlock S.SBGeneratedQuantities $ do
    let ps = indexed matchupT favoriteG muVecE :> toVec matchupT sigmaE :> TNil
    _ <- S.addFromCodeWriter $ S.declareRHSNW (S.NamedDeclSpec "eScoreDiff" $ S.vectorSpec (S.dataSetSizeE matchupT))
         $ S.familyRNG S.normalDist ps
    pure ()

  -- log-likelihood
  S.generateLogLikelihood resultsT S.normalDist
    (pure (\k -> (indexed resultsT favoriteG muVecE) !! k :> (toVec resultsT sigmaE) !! k :> TNil))
    (pure $ \k -> spreadDiffE !! k)


-- the getParameter function feels like an incantation.  Need to simplify.
type ModelReturn = ([(Text, [Double])], [Double], [Double],[(Text, [Double])])
normalParamCIs :: K.KnitEffects r => S.ResultAction ModelData GQData S.DataSetGroupIntMaps r () ModelReturn
normalParamCIs = S.UseSummary f where
  f summary _ modelDataAndIndexes_C mGQDataAndIndexes_C = do
    let favoriteG = S.GroupTypeTag @Text "Favorite"
    resultIndexesE <- K.ignoreCacheTime $ fmap snd modelDataAndIndexes_C
    teamResultIM <- K.knitEither
      $  resultIndexesE >>= S.getGroupIndex (S.RowTypeTag @_ @FB_Result S.ModelDataT "Results") favoriteG

    gqDataAndIndexes_C <- K.knitMaybe "normalParamCIs: No GQ data/indices provided!" mGQDataAndIndexes_C
    matchupIndexesE <- K.ignoreCacheTime $ fmap snd gqDataAndIndexes_C
    teamMatchupIM <- K.knitEither
                     $ matchupIndexesE >>= S.getGroupIndex (S.RowTypeTag @_ @FB_Matchup S.GQDataT "Matchups") favoriteG
    K.logLE K.Diagnostic $ "MatchupIM: " <> show teamMatchupIM
    let resultsTeamList = fmap snd $ IM.toAscList teamResultIM
        matchupsTeamList = fmap snd $ IM.toAscList teamMatchupIM
    let getScalar n = K.knitEither $ S.getScalar . fmap CS.percents <$> S.parseScalar n (CS.paramStats summary)
        getVector n = K.knitEither $ S.getVector . fmap CS.percents <$> S.parse1D n (CS.paramStats summary)
        addTeams t = fmap (zip t . Vec.toList)
    (,,,) <$> addTeams resultsTeamList (getVector "mu_fav")
      <*> getScalar "sigma_mu_fav"
      <*> getScalar "sigma"
      <*> addTeams matchupsTeamList (getVector "eScoreDiff")
