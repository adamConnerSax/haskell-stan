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

import qualified Stan.Language as SL
import Stan.Language (TypedList(..))
import qualified Stan.Functions as SF
import Stan.Functions.Operators
import qualified Stan.Builder as SB
import qualified Stan.BuildingBlocks as SBB
import qualified Stan.Runner as SR
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
type instance SB.DataSource SB.ModelDataT = F.Frame FB_Result
type instance SB.DataSource SB.GQDataT = F.Frame FB_Matchup

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
  ModelDataPkg { resultsT :: SB.RowTypeTag SB.ModelDataT FB_Result
               , homeFieldG :: SB.GroupTypeTag HomeField
               , favoriteG :: SB.GroupTypeTag Text
               , favoriteSize :: SL.IntE
               , underDogG :: SB.GroupTypeTag Text
               }

data GQDataPkg = GQDataPkg { matchupsT :: SB.RowTypeTag SB.GQDataT FB_Matchup }

homeField :: FB_Result -> HomeField
homeField r = if r ^. home then FavoriteField else UnderdogField

scoreDiff :: FB_Result -> Double
scoreDiff r = realToFrac (r ^. favorite) - realToFrac (r ^. underdog)

spreadDiff :: FB_Result -> Double
spreadDiff r = r ^. spread - scoreDiff r

modelDataBuilder :: Foldable f => f Text -> SB.StanDataBuilderEff SB.ModelDataT ModelDataPkg
modelDataBuilder teams = do
  resultsT <- SB.addData "Results" SB.ModelData (SB.ToFoldable id)
  (homeFieldG, _) <- SB.addGroup "HomeField" 2
  (favoriteG, favoriteSize) <- SB.addGroup "Favorite" $ FL.fold FL.length teams
  (underdogG, _) <- SB.addGroup @Text "Underdog" $ FL.fold FL.length teams
  SB.addGroupIndexForData homeFieldG resultsT $ SB.makeIndexFromEnum homeField
  SB.addGroupIndexForData favoriteG resultsT $ SB.makeIndexFromFoldable show (F.rgetField @FavoriteName) teams
  SB.addGroupIntMapForData favoriteG resultsT $ SB.dataToIntMapFromFoldable (F.rgetField @FavoriteName) teams
  pure $ ModelDataPkg resultsT homeFieldG favoriteG favoriteSize underdogG

gqDataBuilder :: Foldable f => f Text -> ModelDataPkg -> SB.StanDataBuilderEff SB.GQDataT GQDataPkg
gqDataBuilder teams mdp = do
   matchupDataT <- SB.addData "Matchups" SB.GQData (SB.ToFoldable id)
   SB.addGroupIndexForData (favoriteG mdp) matchupDataT $ SB.makeIndexFromFoldable show (F.rgetField @FavoriteName) teams
   SB.addGroupIntMapForData (favoriteG mdp) matchupDataT $ SB.dataToIntMapFromFoldable (F.rgetField @FavoriteName) teams
   pure $ GQDataPkg matchupDataT

spreadDiffNormal :: ModelDataPkg -> GQDataPkg -> SB.StanModelBuilderEff ()
spreadDiffNormal (ModelDataPkg resultsT homeFieldG favoriteG favoriteSize underDogG) (GQDataPkg matchupT) = do
  spreadDiffE <- SBB.addRealData resultsT "diff" Nothing Nothing spreadDiff

  -- parameters
  sigmaMuP <- SB.simpleParameter
              (SL.NamedDeclSpec "sigma_mu_fav" $ SL.addVMs (SL.Modifiers [SL.lowerM $ SL.realE 0]) SL.realSpec)
              (SB.given (SL.realE 0) :> SB.given (SL.realE 3) :> TNil)
              SF.normal
  sigmaP <- SB.simpleParameter
         (SL.NamedDeclSpec "sigma" $ SL.addVMs (SL.Modifiers [SL.lowerM $ SL.realE 0]) SL.realSpec)
         (SB.given (SL.realE 13) :> SB.given (SL.realE 15) :> TNil)
         $ SF.normal
  muVP <- SB.simpleParameter
          (SL.NamedDeclSpec "mu_fav" $ SL.vectorSpec favoriteSize)
          (SB.given (SL.realE 0) :> sigmaMuP :> TNil)
          $ SF.normalS

  -- get expressions for the parameters we need to model the data
  let (sigmaE :> muVecE :> TNil) = SB.parametersAsExprs (sigmaP :> muVP :> TNil)

  -- helper functions
  let toVec rtt x = SF.rep_vector x (SB.dataSetSizeE rtt)
      indexed rtt gtt = SL.indexE SL.s0 (SB.dataByGroupIndexE rtt gtt)

  -- model (non-parameter part)
  SB.inBlock SL.SBModel
    $ SB.addStmtToCode
    $ SBB.familySample SBB.normalDist spreadDiffE (indexed resultsT favoriteG muVecE :> toVec resultsT sigmaE :> TNil)

  -- generated quantities, in this case a prediction
  SB.inBlock SL.SBGeneratedQuantities $ do
    let ps = indexed matchupT favoriteG muVecE :> toVec matchupT sigmaE :> TNil
    _ <- SB.addFromCodeWriter $ SL.declareRHSNW (SL.NamedDeclSpec "eScoreDiff" $ SL.vectorSpec (SB.dataSetSizeE matchupT))
         $ SBB.familyRNG SBB.normalDist ps
    pure ()

  -- log-likelihood
  SBB.generateLogLikelihood resultsT SBB.normalDist
    (pure (\k -> (indexed resultsT favoriteG muVecE) !! k :> (toVec resultsT sigmaE) !! k :> TNil))
    (pure $ \k -> spreadDiffE !! k)


-- the getParameter function feels like an incantation.  Need to simplify.
type ModelReturn = ([(Text, [Double])], [Double], [Double],[(Text, [Double])])
normalParamCIs :: K.KnitEffects r => SR.ResultAction r SB.DataSetGroupIntMaps () ModelReturn
normalParamCIs = SR.UseSummary f where
  f summary _ modelDataAndIndexes_C mGQDataAndIndexes_C = do
    let favoriteG = SB.GroupTypeTag @Text "Favorite"
    resultIndexesE <- K.ignoreCacheTime $ fmap snd modelDataAndIndexes_C
    teamResultIM <- K.knitEither
      $  resultIndexesE >>= SB.getGroupIndex (SB.RowTypeTag @_ @FB_Result SB.ModelData "Results") favoriteG

    gqDataAndIndexes_C <- K.knitMaybe "normalParamCIs: No GQ data/indices provided!" mGQDataAndIndexes_C
    matchupIndexesE <- K.ignoreCacheTime $ fmap snd gqDataAndIndexes_C
    teamMatchupIM <- K.knitEither
                     $ matchupIndexesE >>= SB.getGroupIndex (SB.RowTypeTag @_ @FB_Matchup SB.GQData "Matchups") favoriteG
    K.logLE K.Diagnostic $ "MatchupIM: " <> show teamMatchupIM
    let resultsTeamList = fmap snd $ IM.toAscList teamResultIM
        matchupsTeamList = fmap snd $ IM.toAscList teamMatchupIM
    let getScalar n = K.knitEither $ SR.getScalar . fmap CS.percents <$> SR.parseScalar n (CS.paramStats summary)
        getVector n = K.knitEither $ SR.getVector . fmap CS.percents <$> SR.parse1D n (CS.paramStats summary)
        addTeams t = fmap (zip t . Vec.toList)
    (,,,) <$> addTeams resultsTeamList (getVector "mu_fav")
      <*> getScalar "sigma_mu_fav"
      <*> getScalar "sigma"
      <*> addTeams matchupsTeamList (getVector "eScoreDiff")
