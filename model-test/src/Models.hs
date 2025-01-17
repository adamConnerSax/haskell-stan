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


{-}
import qualified Stan.ModelBuilder.TypedExpressions.DAG as DAG
import qualified Stan.ModelBuilder.TypedExpressions.DAGTypes as DAG
import qualified Stan.ModelBuilder.TypedExpressions.Indexing as TE
import qualified Stan.ModelBuilder.TypedExpressions.Types as TE
import qualified Stan.ModelBuilder.TypedExpressions.TypedList as TE
import Stan.ModelBuilder.TypedExpressions.TypedList (TypedList(..))
import qualified Stan.ModelBuilder.TypedExpressions.Expressions as TE
import qualified Stan.ModelBuilder.TypedExpressions.Statements as TE
import qualified Stan.ModelBuilder.TypedExpressions.StanFunctions as TE
import Stan.ModelBuilder.TypedExpressions.Recursion (hfmap)

import qualified Stan.ModelBuilder.BuildingBlocks as SBB
--import qualified Stan.ModelBuilder.Expressions as SE
import qualified Stan.ModelBuilder.Distributions as SD
--import qualified Stan.ModelBuilder.GroupModel as SGM
import qualified Stan.ModelConfig as SC
import qualified Stan.Parameters as SP

import qualified Stan.ModelBuilder.TypedExpressions.DAG as SB
import qualified Stan.ModelBuilder.TypedExpressions.DAG as DAG
import Stan.ModelBuilder (groupSizeE)
import qualified Stan.ModelBuilder as TE
import qualified Stan.ModelBuilder as DS

-}

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

homeField :: FB_Result -> HomeField
homeField r = if r ^. home then FavoriteField else UnderdogField

--homeFieldG :: SB.GroupTypeTag HomeField = SB.GroupTypeTag "HomeField"

--favoriteG :: SB.GroupTypeTag Text = SB.GroupTypeTag "Favorite"

--underdogG :: SB.GroupTypeTag Text = SB.GroupTypeTag "Underdog"

-- spread :: F.Record FB_Results -> Double
-- spread = F.rgetField @Spread

scoreDiff :: FB_Result -> Double
scoreDiff r = realToFrac (r ^. favorite) - realToFrac (r ^. underdog)

spreadDiff :: FB_Result -> Double
spreadDiff r = r ^. spread - scoreDiff r

spreadDiffNormal :: Foldable f => f Text -> SB.StanBuilderEff ()
spreadDiffNormal teams = do
  -- data
  resultsData <- SB.addData "Results" SB.ModelData (SB.ToFoldable id)
  (homeFieldG, _) <- SB.addGroup "HomeField" 2
  (favoriteG, favoriteSize) <- SB.addGroup "Favorite" $ FL.fold FL.length teams
  (underdogG, _) <- SB.addGroup @Text "Underdog" $ FL.fold FL.length teams
  SB.addGroupIndexForData homeFieldG resultsData $ SB.makeIndexFromEnum homeField
  SB.addGroupIndexForData favoriteG resultsData $ SB.makeIndexFromFoldable show (F.rgetField @FavoriteName) teams
  SB.addGroupIntMapForData favoriteG resultsData $ SB.dataToIntMapFromFoldable (F.rgetField @FavoriteName) teams
  matchupData <- SB.addData "Matchups" SB.GQData (SB.ToFoldable id)
  SB.addGroupIndexForData favoriteG matchupData $ SB.makeIndexFromFoldable show (F.rgetField @FavoriteName) teams

  spreadDiffE <- SBB.addRealData resultsData "diff" Nothing Nothing spreadDiff

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

  -- helpers for broadcasting sigma and indexing mu
  let toVec rtt x = SF.rep_vector x (SB.dataSetSizeE rtt)
      indexed rtt gtt = SL.indexE SL.s0 (SB.dataByGroupIndexE rtt gtt)

  -- model (non-parameter part)
  SB.inBlock SL.SBModel
    $ SB.addStmtToCode
    $ SBB.familySample SBB.normalDist spreadDiffE (indexed resultsData favoriteG muVecE :> toVec resultsData sigmaE :> TNil)

  -- generated quantities, in this case a prediction
  SB.inBlock SL.SBGeneratedQuantities $ do
    let ps = indexed matchupData favoriteG muVecE :> toVec matchupData sigmaE :> TNil
--    SB.addRowKeyIntMap matchupsData favoriteG (F.rgetField @FavoriteName)
    _ <- SB.addFromCodeWriter $ SL.declareRHSNW (SL.NamedDeclSpec "eScoreDiff" $ SL.vectorSpec (SB.dataSetSizeE matchupData))
         $ SBB.familyRNG SBB.normalDist ps
    pure ()

  -- log-likelihood
  SBB.generateLogLikelihood resultsData SBB.normalDist
    (pure (\k -> (indexed resultsData favoriteG muVecE) !! k :> (toVec resultsData sigmaE) !! k :> TNil))
    (pure $ \k -> spreadDiffE !! k)

--  (return (S.var mu_favV, S.var sigmaV)) spreadDiffV


-- the getParameter function feels like an incantation.  Need to simplify.
type ModelReturn = ([(Text, [Double])],[Double], [Double],[(Text, [Double])])
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
