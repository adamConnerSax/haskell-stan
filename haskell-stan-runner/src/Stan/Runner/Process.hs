{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Stan.Runner.Process
  (
    module Stan.Runner.Process
  , module CmdStan
  , UnwrapJSON
  )
where

import CmdStan
       ( StanExeConfig (..),
         StanSummary,
         StancConfig (..),
         makeDefaultStancConfig,
       )

import qualified Stan.Builder as SB
import qualified Stan.Runner.Config as SRC
import qualified Stan.Runner.RScripts as SRR
import Stan.Runner.RScripts (UnwrapJSON)
import qualified Stan.Runner.SamplerCSV as SCSV
import qualified System.Directory as Dir
import qualified System.Environment as Env
import qualified Relude.Extra as Relude
import qualified Stan.Language.Program as SLP
import qualified Stan.Builder.Parameters.Core as SBPC
import qualified CmdStan as CS
import qualified CmdStan.Types as CS
import qualified Data.Aeson as A
import qualified Data.Aeson.Encoding as A
import qualified Data.ByteString.Lazy as BL
import qualified Data.Text as T
import qualified Data.Text.IO as T
import qualified Knit.Effect.AtomicCache as K (cacheTime)
import qualified Knit.Report as K
import qualified Polysemy as P
import qualified Say

import qualified Control.Exception as X
import qualified GHC.IO.Exception as X

-- simplified runner for common cases
runModel' :: forall st cd md gq (b :: Type -> Type) c r.
             (SRC.KnitStan st cd r
             , st c
             )
          => Either Text Text
          -> Either SRC.ModelRunnerConfig SRC.RunnerInputNames
          -> Maybe SRC.StanMCParameters
          -> SRC.DataWrangler md gq b ()
          -> SLP.StanProgram
          -> SRC.ResultAction md gq b r () c
          -> RScripts
          -> K.ActionWithCacheTime r md
          -> K.ActionWithCacheTime r gq
          -> K.Sem r (K.ActionWithCacheTime r c)
runModel' cacheDirE configE mStanParams dataWrangler stanProgram resultAction rScripts modelData_C gqData_C =
  K.wrapPrefix "runModel'" $ do
  K.logLE K.Diagnostic "building config"
  (rin, stanConfig) <- case configE of
    Left mrc -> pure (SRC.mrcInputNames mrc, mrc)
    Right rin' -> do
      let stancConfig =
            (CS.makeDefaultStancConfig (toString $ SRC.rinModelDir rin' <> "/" <> SRC.rinModel rin')) {CS.useOpenCL = False}
      stanConfig <-
        SRC.setSigFigs 4
        . SRC.noLogOfSummary
        <$> makeDefaultModelRunnerConfig @st @cd
        rin'
        (Just (SLP.All, stanProgram))
        (fromMaybe (SRC.StanMCParameters 4 4 Nothing Nothing Nothing Nothing (Just 1)) mStanParams)
        (Just stancConfig)
      pure (rin', stanConfig)
  let outputLabel = SRC.rinModel rin  <> "_" <> SRC.rinData rin <> maybe "" ("_" <>) (SRC.gqDataName <$> SRC.rinGQ rin)
      cacheKey d = d <> outputLabel <> ".bin"
  resultCacheKey <- case cacheDirE of
    Left d -> do
      K.logLE K.Diagnostic "clearing caches for a fresh run"
      deleteStaleFiles @st @cd stanConfig [StaleData]
      K.clearIfPresent @Text @cd $ cacheKey d
      pure $ cacheKey d
    Right d -> pure $ cacheKey d
  K.logLE K.Info
    $ "Running/retrieving: model="
    <> SRC.rinModel rin <> " using model data=" <> SRC.rinData rin
    <> maybe "" (" and GQ data=" <>) (SRC.gqDataName <$> SRC.rinGQ rin)
  modelDep <- SRC.modelDependency SRC.MRFull $ SRC.mrcInputNames stanConfig
  K.logLE (K.Debug 1) $ "modelDep: " <> show (K.cacheTime modelDep)
  K.logLE (K.Debug 1) $ "modelDataDep: " <> show (K.cacheTime modelData_C)
  K.logLE (K.Debug 1) $ "gqDataDep: " <> show (K.cacheTime gqData_C)
  K.logLE (K.Debug 1) $ "resultCacheKey: " <> resultCacheKey
  let dataModelDep = (,,) <$> modelDep <*> modelData_C <*> gqData_C
  K.retrieveOrMake @st @cd resultCacheKey dataModelDep $ \_ -> do
    K.logLE K.Diagnostic "Data or model newer then last cached result. (Re)-running..."
    runModel @st @cd
      stanConfig
      rScripts
      dataWrangler
      SRC.UnCacheable
      SRC.UnCacheable
      resultAction
      ()
      modelData_C
      gqData_C

-- given cached model data and gq data, a group builder and a model builder
-- generate a no-predictions data-wrangler and program
dataWranglerAndCode :: forall a md gq b r . (K.KnitEffects r)
                    => K.ActionWithCacheTime r md
                    -> K.ActionWithCacheTime r gq
                    -> SB.StanDataBuilderEff SB.ModelDataT md a
                    -> (a -> SB.StanDataBuilderEff SB.GQDataT gq b)
                    -> (a -> b -> SB.StanModelBuilderEff md gq ())
                    -> K.Sem r (SRC.DataWrangler md gq SB.DataSetGroupIntMaps (), SLP.StanProgram)
dataWranglerAndCode modelData_C gqData_C modelDB gqDBF sbF = do
  modelDat <- K.ignoreCacheTime modelData_C
  gqDat <- K.ignoreCacheTime gqData_C
  (bs, _builderLogs, ()) <- K.knitEither $ SBPC.runStanBuilderDAG modelDat gqDat modelDB gqDBF sbF
  let modelWrangle x = (SB.intMapsFromRowInfos (SB.modelRowBuilders bs) x,  SB.modelJsonE bs)
      gqWrangle x = (SB.intMapsFromRowInfos (SB.gqRowBuilders bs) x,  SB.gqJsonE bs)
      wrangler ::  SRC.DataWrangler md gq SB.DataSetGroupIntMaps ()
      wrangler = SRC.Wrangle SRC.TransientIndex modelWrangle (Just gqWrangle)
  pure (wrangler, SB.program (SB.code bs))


makeDefaultModelRunnerConfig :: forall st cd r. SRC.KnitStan st cd r
  => SRC.RunnerInputNames
  -- | Assume model file exists when Nothing.  Otherwise generate from this and use.
  -> Maybe (SLP.GeneratedQuantities, SLP.StanProgram)
  -> SRC.StanMCParameters
  -> Maybe CS.StancConfig
  -> K.Sem r SRC.ModelRunnerConfig
makeDefaultModelRunnerConfig runnerInputNames modelM stanMCParameters mStancConfig = do
  let doOnlyLL = case modelM of
        Nothing -> False
        Just (_, p) ->  SLP.programHasLLBlock p
  let doOnlyPP = case modelM of
        Nothing -> False
        Just (_, p) ->  SLP.programHasPPBlock p
      stanMakeConfig mr = do
        K.logLE K.Diagnostic $ "Making config for " <> show mr <> " run."
        writeModel runnerInputNames mr modelM
        stanMakeNoGQConfig' <- K.liftKnit $ CS.makeDefaultMakeConfig (toString $ SRC.modelPath mr runnerInputNames)
        return $  stanMakeNoGQConfig' {CS.stancFlags = mStancConfig}
  stanMakeNoGQConfig <- stanMakeConfig SRC.MRNoGQ
  stanMakeOnlyLLConfig <- stanMakeConfig SRC.MROnlyLL
  stanMakeOnlyPPConfig <- stanMakeConfig SRC.MROnlyPP
  stanMakeFullConfig <- stanMakeConfig SRC.MRFull
  let makeConfigs :: SRC.ModelRun -> CS.MakeConfig
      makeConfigs SRC.MRNoGQ = stanMakeNoGQConfig
      makeConfigs SRC.MROnlyLL = stanMakeOnlyLLConfig
      makeConfigs SRC.MROnlyPP = stanMakeOnlyPPConfig
      makeConfigs SRC.MRFull = stanMakeFullConfig
  stanSummaryConfig <- do
    K.logLE K.Diagnostic "Making summary config"
    K.liftKnit $ CS.useCmdStanDirForStansummary (CS.makeDefaultSummaryConfig [])
  return $
    SRC.ModelRunnerConfig
      doOnlyLL
      doOnlyPP
      makeConfigs
      stanSummaryConfig
      runnerInputNames
      stanMCParameters
      True
      True
{-# INLINEABLE makeDefaultModelRunnerConfig #-}

modelGQ :: SRC.ModelRun -> SLP.GeneratedQuantities -> SLP.GeneratedQuantities
modelGQ SRC.MRNoGQ _ = SLP.NoGQ
modelGQ SRC.MROnlyLL _ = SLP.OnlyLL
modelGQ SRC.MROnlyPP _ = SLP.OnlyPP
modelGQ SRC.MRFull _ = SLP.NeitherLL_PP

writeModel :: K.KnitEffects r
  => SRC.RunnerInputNames
  -> SRC.ModelRun
  -- | Assume model file exists when Nothing.  Otherwise generate from this and use.
  -> Maybe (SLP.GeneratedQuantities, SLP.StanProgram)
  -> K.Sem r ()
writeModel runnerInputNames modelRun modelM = do
  let modelDir = SRC.rinModelDir runnerInputNames
      mName = SRC.modelName modelRun runnerInputNames
  case modelM of
    Nothing -> return ()
    Just (gq', m) -> do
      K.logLE K.Diagnostic "Creating model code directory if neccessary."
      createDirIfNecessary modelDir
      let gq = modelGQ modelRun gq'
      K.logLE K.Diagnostic "Renaming old if neccessary, writing if new."
      modelState <- renameAndWriteIfNotSame gq m modelDir mName
      case modelState of
        New -> K.logLE K.Diagnostic "Given model was new."
        Same -> K.logLE K.Diagnostic "Given model was the same as existing model file."
        Updated newName -> K.logLE K.Diagnostic
                           $ "Given model was different from exisiting.  Old one was moved to \""
                           <> newName <> "\"."
{-# INLINEABLE writeModel #-}

sampleExeConfig :: SRC.RunnerInputNames -> SRC.StanMCParameters -> CS.StanExeConfig
sampleExeConfig rin smp =
    (CS.makeDefaultSample (toString $  SRC.modelName SRC.MRNoGQ rin) Nothing)
    { CS.inputData = Just (SRC.dataDirPath rin $ SRC.combinedDataFileName rin)
    , CS.output = Just (SRC.outputDirPath rin $ SRC.outputPrefix SRC.MRNoGQ rin <> ".csv")
    , CS.numChains = Just $ SRC.smcNumChains smp
    , CS.numThreads = Just $ SRC.smcNumThreads smp
    , CS.numSamples = SRC.smcNumSamplesM smp
    , CS.numWarmup = SRC.smcNumWarmupM smp
    , CS.adaptDelta = SRC.smcAdaptDeltaM smp
    , CS.maxTreeDepth = SRC.smcMaxTreeDepth smp
    , CS.randomSeed = SRC.smcRandomSeed smp
    }
{-# INLINEABLE sampleExeConfig #-}

gqExeConfig :: SRC.ModelRun
                -> SRC.RunnerInputNames
                -> SRC.StanMCParameters
                -> Int
                -> CS.StanExeConfig
gqExeConfig mr rin smp n = do
  let dataFileName = case mr of
        SRC.MRNoGQ -> error "modelRun=MrNoGQ set in gqExeConfig"
        SRC.MRFull -> SRC.combinedDataFileName rin
        _ -> SRC.modelDataFileName rin
  (CS.makeDefaultGenerateQuantities (toString $ SRC.modelName mr rin) n)
    { CS.inputData = Just (SRC.dataDirPath rin dataFileName)
    , CS.fittedParams = Just (SRC.outputDirPath rin $ SRC.outputPrefix SRC.MRNoGQ rin <> "_" <> show n <> ".csv")
    , CS.output = Just (SRC.outputDirPath rin $ SRC.outputPrefix mr rin <> "_" <> show n <> ".csv")
    , CS.randomSeed = SRC.smcRandomSeed smp
    }
{-# INLINEABLE gqExeConfig #-}

data RScripts = None | ShinyStan [SRR.UnwrapJSON] | Loo | Both [SRR.UnwrapJSON] deriving stock (Show, Eq, Ord)
looOf :: RScripts -> RScripts
looOf None = None
looOf (ShinyStan _) = None
looOf Loo = Loo
looOf (Both _) = Loo

shinyOf :: RScripts -> RScripts
shinyOf None = None
shinyOf x@(ShinyStan _) = x
shinyOf Loo = None
shinyOf (Both x) = ShinyStan x

writeRScripts :: forall st cd r. SRC.KnitStan st cd r => RScripts -> SRC.ModelRun -> SRC.ModelRunnerConfig -> K.Sem r ()
writeRScripts rScripts mr config = do
  let scriptPrefix = SRC.mergedPrefix mr $ SRC.mrcInputNames config
      write mSuffix t = writeFileText (SRC.rDirPath (SRC.mrcInputNames config) scriptPrefix   <> fromMaybe "" mSuffix <> ".R") t
      writeShiny ujs = write (Just "_shinystan") $ SRR.shinyStanScript mr config ujs
      writeLoo = write Nothing $ SRR.looScript mr config Nothing 10
  case rScripts of
    None -> pure ()
    ShinyStan ujs -> writeShiny ujs
    Loo -> writeLoo
    Both ujs -> writeShiny ujs >> writeLoo
{-# INLINEABLE writeRScripts #-}

wrangleDataWithoutPredictions :: forall st cd md gq b r.
  (SRC.KnitStan st cd r)
  => SRC.ModelRunnerConfig
  -> SRC.DataWrangler md gq b ()
  -> SRC.Cacheable st (b md)
  -> SRC.Cacheable st (b gq)
  -> K.ActionWithCacheTime r md
  -> K.ActionWithCacheTime r gq
  -> K.Sem r (K.ActionWithCacheTime r (Either T.Text (b md))
             , K.ActionWithCacheTime r (Either T.Text (b gq))
             )
wrangleDataWithoutPredictions config dw cbm cbgq md_C gq_C = wrangleData @st @cd config dw cbm cbgq md_C gq_C ()
{-# INLINE wrangleDataWithoutPredictions #-}

{-
This, I think, generates the indexes *and* the JSON, and saves the JSON to the appropriate file.
But the JSON is just for Stan so we don't return it from the function. But the cache time here
holds the newer of the index and the JSON since we do want to know if anything downstream needs
to be re-run given either the JSON or index cache time.
-}
wrangleData :: forall st cd md gq b p r.SRC.KnitStan st cd r
  => SRC.ModelRunnerConfig
  -> SRC.DataWrangler md gq b p
  -> SRC.Cacheable st (b md)
  -> SRC.Cacheable st (b gq)
  -> K.ActionWithCacheTime r md
  -> K.ActionWithCacheTime r gq
  -> p
  -> K.Sem r (K.ActionWithCacheTime r (Either T.Text (b md))
             , K.ActionWithCacheTime r (Either T.Text (b gq))
             )
wrangleData config w cbm cbgq md_C gq_C p = K.wrapPrefix "wrangleData" $ do
  K.logLE K.Diagnostic "Wrangling Data..."
  let (indexerType, modelIndexAndEncoder, mGQIndexAndEncoder) = case w of
        SRC.Wrangle x y z -> (x, y, z)
        SRC.WrangleWithPredictions x y z _ -> (x, y, z)
  curModelData_C <- SRC.modelDataDependency $ SRC.mrcInputNames config
  (newModelData_C, modelIndexes_C) <- wranglerPrep @st @cd config SB.ModelDataT indexerType modelIndexAndEncoder cbm md_C
  modelJSON_C <- K.updateIf curModelData_C newModelData_C $ \e -> do
    let modelDataFileName = SRC.modelDataFileName $ SRC.mrcInputNames config
    K.logLE K.Diagnostic $ "existing model json (" <> modelDataFileName  <> ") appears older than cached data."
    jsonEncoding <- K.knitEither e
    K.liftKnit . BL.writeFile (SRC.dataDirPath (SRC.mrcInputNames config) modelDataFileName)
      $ A.encodingToLazyByteString $ A.pairs jsonEncoding
  let model_C = const <$> modelIndexes_C <*> modelJSON_C
  genQ_C <- case mGQIndexAndEncoder of
    Nothing -> pure $ pure $ Left "wrangleData: Attempt to use GQ indexes but No GQ wrangler given."
    Just gqIndexAndEncoder -> do
      mGQData_C <- SRC.gqDataDependency $ SRC.mrcInputNames config
      case mGQData_C of
        Nothing -> pure $ pure $ Left "wrangleData: Attempt to wrangle GQ data but config.mrcInputNames.rinQG is Nothing."
        Just gqData_C -> do
          K.logLE K.Diagnostic "Wrangling GQ Data"
          (newGQData_C, gqIndexes_C) <- wranglerPrep @st @cd config SB.GQDataT indexerType gqIndexAndEncoder cbgq gq_C
          let gqJSONDeps = (,,) <$> newGQData_C <*> modelIndexes_C <*> gqIndexes_C
          gqJSON_C <- K.updateIf gqData_C gqJSONDeps $ \(e, meb, gqeb) -> do
            gqDataFileName <- K.knitMaybe "Attempt to build gq json but rinGQ is Nothing." $ SRC.gqDataFileName $ SRC.mrcInputNames config
            K.logLE K.Diagnostic $ "existing GQ json (" <> gqDataFileName  <> ") appears older than cached data."
            jsonEncoding <- K.knitEither e
            indexEncoding <- case w of
              SRC.Wrangle _ _ _ -> return mempty
              SRC.WrangleWithPredictions _ _ _ encodeToPredict -> K.knitEither $ encodeToPredict meb gqeb p
            writeFileLBS (SRC.dataDirPath (SRC.mrcInputNames config) gqDataFileName)
              $ A.encodingToLazyByteString $ A.pairs (jsonEncoding <> indexEncoding)
          return $ const <$> gqIndexes_C <*> gqJSON_C
  return (model_C, genQ_C)
{-# INLINEABLE wrangleData #-}

-- create function to rebuild json along with time stamp from data used
wranglerPrep :: forall st cd d (b :: Type -> Type) r.
  SRC.KnitStan st cd r
  => SRC.ModelRunnerConfig
  -> SB.InputDataT
  -> SRC.DataIndexerType b
  -> SRC.Wrangler d b
  -> SRC.Cacheable st (b d)
  -> K.ActionWithCacheTime r d
  -> K.Sem r (K.ActionWithCacheTime r (Either Text A.Series), K.ActionWithCacheTime r (Either T.Text (b d)))
wranglerPrep config inputDataType indexerType wrangler cb a_C = do
  let indexAndEncoder_C = fmap wrangler a_C
      eb_C = fmap fst indexAndEncoder_C
      encoder_C = fmap snd indexAndEncoder_C
  index_C <- manageIndex @d @b @st @cd config inputDataType indexerType cb eb_C
  let newJSON_C = encoder_C <*> a_C
  return (newJSON_C, index_C)
{-# INLINEABLE wranglerPrep #-}

-- if we are caching the index (not sure this is ever worth it!)
-- here is where we check if that cache needs updating.  Otherwise we
-- just return it
manageIndex :: forall d b st cd r.
  SRC.KnitStan st cd r
  => SRC.ModelRunnerConfig
  -> SB.InputDataT
  -> SRC.DataIndexerType b
  -> SRC.Cacheable st (b d)
  -> K.ActionWithCacheTime r (Either T.Text (b d))
  -> K.Sem r (K.ActionWithCacheTime r (Either T.Text (b d)))
manageIndex config inputDataType dataIndexer cb ebFromA_C = do
  case dataIndexer of
    SRC.CacheableIndex indexCacheKey ->
      case cb of
        SRC.Cacheable -> do
          curJSON_C <- case inputDataType of
            SB.ModelDataT -> SRC.modelDataDependency (SRC.mrcInputNames config)
            SB.GQDataT -> do
              mGQJSON_C <- SRC.gqDataDependency (SRC.mrcInputNames config)
              K.knitMaybe "ModelRunner.manageIndex called with input type GQ but no GQ setup." mGQJSON_C
          when (isNothing $ K.cacheTime curJSON_C) $ do
            let jsonFP = case inputDataType of
                  SB.ModelDataT -> SRC.modelDataFileName $ SRC.mrcInputNames config
                  SB.GQDataT -> fromMaybe "Error:No GQ Setup" $ SRC.gqDataFileName $ SRC.mrcInputNames config
            K.logLE (K.Debug 1)  $ "JSON data (\"" <> jsonFP <> "\") is missing.  Deleting cached indices to force rebuild."
            K.clearIfPresent @Text @cd (indexCacheKey config inputDataType)
          K.retrieveOrMake @st @cd (indexCacheKey config inputDataType) ebFromA_C pure
        _ -> K.knitError "Cacheable index type provided but b is Uncacheable."
    _ -> pure ebFromA_C
{-# INLINEABLE manageIndex #-}

-- where do we combine data??
runModel :: forall st cd md gq b p c r.
  (SRC.KnitStan st cd r)
  => SRC.ModelRunnerConfig
  -> RScripts
  -> SRC.DataWrangler md gq b p
  -> SRC.Cacheable st (b md)
  -> SRC.Cacheable st (b gq)
  -> SRC.ResultAction md gq b r p c
  -> p
  -> K.ActionWithCacheTime r md
  -> K.ActionWithCacheTime r gq
  -> K.Sem r c
runModel config rScriptsToWrite dataWrangler cbm cbgq makeResult toPredict md_C gq_C = K.wrapPrefix "Stan.ModelRunner.runModel" $ do
  K.logLE K.Info "running Model (if necessary)"
  let runnerInputNames = SRC.mrcInputNames config
      stanMCParameters = SRC.mrcStanMCParameters config
  checkCPPEnv
  createDirIfNecessary (SRC.mrcModelDir config)
  createDirIfNecessary (SRC.mrcModelDir config <> "/data") -- json inputs
  createDirIfNecessary (SRC.mrcModelDir config <> "/output") -- csv model run output
  createDirIfNecessary (SRC.mrcModelDir config <> "/R") -- scripts to load fit into R for shinyStan or loo.
  -- create/update JSON (if nec) and retrieve/update/create indices (b i)
  (modelIndices_C, gqIndices_C) <- wrangleData @st @cd config dataWrangler cbm cbgq md_C gq_C toPredict
  curModelNoGQ_C <- SRC.modelDependency SRC.MRNoGQ runnerInputNames --empty action to represent latest update of all deps for no GQ run
  curModel_C <- SRC.modelDependency SRC.MRFull runnerInputNames --empty action to represent latest update of all deps for GQ run
  -- run model and/or build gq samples as necessary
  (modelResDep, mGQResDep) <- do
    let runModelF = do
          let modelExeConfig = sampleExeConfig runnerInputNames stanMCParameters
          K.logLE K.Diagnostic $ "Running Model: " <> SRC.modelName SRC.MRNoGQ runnerInputNames
          K.logLE K.Diagnostic $ "Command: " <> toText (CS.toStanExeCmdLine modelExeConfig)
          K.liftKnit $ CS.stan (SRC.modelPath SRC.MRNoGQ runnerInputNames) modelExeConfig
          K.logLE K.Diagnostic $ "Finished " <> SRC.modelName SRC.MRNoGQ runnerInputNames
        runOneGQ mr n = do
          let exeConfig = gqExeConfig mr runnerInputNames stanMCParameters n
          K.logLE K.Diagnostic $ "Generating " <> show mr
          K.logLE K.Diagnostic $ "Using fitted parameters from model " <> SRC.modelName SRC.MRNoGQ runnerInputNames
          K.logLE K.Diagnostic $ "Command: " <> toText (CS.toStanExeCmdLine exeConfig)
          K.liftKnit $ CS.stan (SRC.modelPath mr runnerInputNames) exeConfig
          K.logLE K.Diagnostic $ "Finished generating " <> show mr
          K.logLE K.Diagnostic "Merging samples..."
          samplesFP <- K.knitMaybe "runModel.runOneGQ: fittedParams field is Nothing in exeConfig"
            $ CS.fittedParams exeConfig
          llFP <- K.knitMaybe "runModel.runOneGQ: output field is Nothing in exeConfig" $ CS.output exeConfig
          let mergedFP = SRC.outputDirPath (SRC.mrcInputNames config)
                $ SRC.mergedPrefix mr runnerInputNames <> "_" <> show n <> ".csv"
          K.liftKnit $ SCSV.appendGQsToSamplerCSV samplesFP llFP mergedFP
    _ <- SRC.combineData (SRC.mrcInputNames config)  -- this only does anything if either data set has changed
    let modelSamplesFileNames =  SRC.samplesFileNames SRC.MRNoGQ config
    modelSamplesFilesDep <- K.oldestUnit <$> traverse K.fileDependency modelSamplesFileNames
    let runModelDeps = (,) <$> modelIndices_C <*> curModelNoGQ_C -- indices carries data update time
    modelRes_C <- K.updateIf modelSamplesFilesDep runModelDeps $ \_ -> do
      K.logLE K.Diagnostic "Stan model outputs older than model input data or model code.  Rebuilding Stan exe and running."
      K.logLE (K.Debug 1) $ "Make CommandLine: " <> toText (CS.makeConfigToCmdLine (SRC.mrcStanMakeConfig config SRC.MRNoGQ))
      K.liftKnit $ CS.make (SRC.mrcStanMakeConfig config SRC.MRNoGQ)
      res <- runModelF
      when (SRC.mrcRunDiagnose config) $ do
        K.logLE K.Info "Running stan diagnostics"
        K.liftKnit $ CS.diagnoseCSD modelSamplesFileNames
      K.logLE K.Diagnostic "writing R scripts for new model run."
      writeRScripts @st @cd (shinyOf rScriptsToWrite) SRC.MRNoGQ config
      return res
    case SRC.mrcDoOnlyLL config of
      False -> K.logLE K.Diagnostic "No onlyLL run indicated by config."
      True -> do
        curModelOnlyLL_C <- SRC.modelDependency SRC.MROnlyLL runnerInputNames
        let runLLDeps  = (,) <$> modelIndices_C <*> curModelOnlyLL_C -- indices carries data update time
        let onlySamplesFileNames = SRC.samplesFileNames SRC.MROnlyLL config
        onlyLLSamplesFileDep <- K.oldestUnit <$> traverse K.fileDependency onlySamplesFileNames
        _ <- K.updateIf onlyLLSamplesFileDep runLLDeps $ \_ -> do
          let llOnlyMakeConfig = SRC.mrcStanMakeConfig config SRC.MROnlyLL
          K.logLE K.Diagnostic "Stan log likelihood  outputs older than model input data or model code. Generating LL."
          K.logLE (K.Debug 1) $ "Make CommandLine: " <> toText (CS.makeConfigToCmdLine llOnlyMakeConfig)
          K.liftKnit $ CS.make llOnlyMakeConfig
          mRes <- maybe Nothing (const $ Just ()) . sequence
                  <$> K.sequenceConcurrently (fmap (runOneGQ SRC.MROnlyLL) [1 .. (SRC.smcNumChains $ SRC.mrcStanMCParameters config)])
          K.knitMaybe "There was an error generating LL for a chain." mRes
        writeRScripts @st @cd (looOf rScriptsToWrite) SRC.MROnlyLL config
        pure ()
    case SRC.mrcDoOnlyPP config of
      False -> K.logLE K.Diagnostic "No onlyPP run indicated by config."
      True -> do
        curModelOnlyPP_C <- SRC.modelDependency SRC.MROnlyPP runnerInputNames
        let runPPDeps  = (,) <$> modelIndices_C <*> curModelOnlyPP_C -- indices carries data update time
        let onlySamplesFileNames = SRC.samplesFileNames SRC.MROnlyPP config
        onlyPPSamplesFileDep <- K.oldestUnit <$> traverse K.fileDependency onlySamplesFileNames
        _ <- K.updateIf onlyPPSamplesFileDep runPPDeps $ \_ -> do
          let ppOnlyMakeConfig = SRC.mrcStanMakeConfig config SRC.MROnlyPP
          K.logLE K.Diagnostic "Stan posterior prediction outputs older than model input data or model code. Generating PP."
          K.logLE (K.Debug 1) $ "Make CommandLine: " <> toText (CS.makeConfigToCmdLine ppOnlyMakeConfig)
          K.liftKnit $ CS.make ppOnlyMakeConfig
          mRes <- maybe Nothing (const $ Just ()) . sequence
                  <$> K.sequenceConcurrently (fmap (runOneGQ SRC.MROnlyPP) [1 .. (SRC.smcNumChains $ SRC.mrcStanMCParameters config)])
          K.knitMaybe "There was an error generating PP for a chain." mRes
        writeRScripts @st @cd (shinyOf rScriptsToWrite) SRC.MROnlyPP config
        pure ()
    mGQRes_C <- case SRC.rinGQ runnerInputNames of
      Nothing -> pure Nothing
      Just _ -> do
        K.logLE K.Diagnostic "Checking if GQs are up to date"
        let runGQDeps = (,,) <$> modelIndices_C <*> gqIndices_C <*> curModel_C
        gqSamplesFileDep <- K.oldestUnit <$> traverse K.fileDependency (SRC.samplesFileNames SRC.MRFull config)
        res_C <- K.updateIf gqSamplesFileDep runGQDeps $ const $ do
          K.logLE K.Diagnostic "Stan GQ outputs older than model input data, GQ input data or model code. Running GQ."
          K.logLE (K.Debug 1) $ "Make CommandLine: " <> toText (CS.makeConfigToCmdLine (SRC.mrcStanMakeConfig config SRC.MRFull))
          K.liftKnit $ CS.make (SRC.mrcStanMakeConfig config SRC.MRFull)
--          SRC.combineData $ SRC.mrcInputNames config
          mRes <- maybe Nothing (const $ Just ()) . sequence
                <$> K.sequenceConcurrently (fmap (runOneGQ SRC.MRFull) [1 .. (SRC.smcNumChains $ SRC.mrcStanMCParameters config)])
          K.knitMaybe "There was an error running GQ for a chain." mRes
        writeRScripts @st @cd (shinyOf rScriptsToWrite) SRC.MRFull config
        pure $ Just res_C
    return (modelRes_C, mGQRes_C)
  let --outputFileNames = SRC.finalSamplesFileNames SRC.MRFull config
      outputDep = case mGQResDep of
        Nothing -> modelResDep
        Just gqResDep -> const <$> gqResDep <*> modelResDep
      makeSummaryFromCSVs csvFileNames summaryPath = do
        K.logLE K.Diagnostic "Stan summary older output.  Re-summarizing."
        K.logLE (K.Debug 1) $
          "Summary command: "
          <> show ((CS.cmdStanDir $ SRC.mrcStanMakeConfig config SRC.MRFull) ++ "/bin/stansummary")
          <> " "
          <> T.intercalate " " (fmap T.pack (CS.stansummaryConfigToCmdLine (SRC.mrcStanSummaryConfig config)))
        K.logLE (K.Debug 1) $ "Stan output ot summarize: "
          <> T.intercalate " " (fmap toText csvFileNames)
        summary <- K.liftKnit $ CS.stansummary ((SRC.mrcStanSummaryConfig config) {CS.sampleFiles = csvFileNames})
        P.embed $ A.encodeFile summaryPath summary
        return summary
      getSummary csvFileNames summaryPath = do
        summaryE <- K.ignoreCacheTimeM
                    $ K.loadOrMakeFile
                    summaryPath
                    ((K.knitEither =<<) . P.embed . Relude.firstF toText . A.eitherDecodeFileStrict . toString)
                    outputDep -- this only is here to carry the timing to compare the output file with
                    (const $ makeSummaryFromCSVs csvFileNames summaryPath)
        K.knitEither $ first toText $ summaryE
      modelResultDeps = (\a b _ -> (a, b)) <$> md_C <*> modelIndices_C <*> modelResDep
      mGQResultDeps = case mGQResDep of
        Nothing -> Nothing
        Just gqResDep -> Just $ (\a b _ -> (a, b)) <$> gq_C <*> gqIndices_C <*> gqResDep
  case makeResult of
    SRC.UseSummary f -> do
      let summaryFileName = SRC.summaryFileName SRC.MRFull config
          samplesFileNames = SRC.finalSamplesFileNames SRC.MRFull config
      summary <-  getSummary samplesFileNames (SRC.outputDirPath (SRC.mrcInputNames config) summaryFileName)
      when (SRC.mrcLogSummary config) $ do
        K.logLE K.Info $ "Stan Summary:\n"
        Say.say $ toText (CS.unparsed summary)
      f summary toPredict modelResultDeps mGQResultDeps
    SRC.SkipSummary f -> f toPredict modelResultDeps mGQResultDeps
    SRC.DoNothing -> pure ()
{-# INLINEABLE runModel #-}

data StaleFiles = StaleData | StaleOutput | StaleSummary deriving stock (Show, Eq, Ord)

deleteStaleFiles :: forall st cd r.SRC.KnitStan st cd r => SRC.ModelRunnerConfig -> [StaleFiles] -> K.Sem r ()
deleteStaleFiles config staleFiles = do
  let samplesFilePaths = concat $ fmap (\mr -> SRC.samplesFileNames mr config) [SRC.MRNoGQ, SRC.MROnlyLL, SRC.MROnlyPP, SRC.MRFull]
      modelSummaryPath = SRC.outputDirPath (SRC.mrcInputNames config) $ SRC.summaryFileName SRC.MRNoGQ config
      gqSummaryPath = SRC.outputDirPath (SRC.mrcInputNames config) $ SRC.summaryFileName SRC.MRFull config
      modelDataPath = SRC.dataDirPath (SRC.mrcInputNames config) $ SRC.modelDataFileName $ SRC.mrcInputNames config
      mGQDataPath = SRC.dataDirPath (SRC.mrcInputNames config) <$> (SRC.gqDataFileName $ SRC.mrcInputNames config)
      toDelete x = case x of
        StaleData -> [modelDataPath] ++ maybe [] one mGQDataPath
        StaleOutput -> samplesFilePaths
        StaleSummary -> [modelSummaryPath, gqSummaryPath]
      exists fp = K.liftKnit $ Dir.doesFileExist fp >>= \x -> return $ if x then Just fp else Nothing
      filesToDelete = ordNub $ concat $ toDelete <$> staleFiles
  extantPaths <- catMaybes <$> traverse exists filesToDelete
  Say.say $ "Deleting output files: " <> T.intercalate "," (toText <$> extantPaths)
  traverse_ (K.liftKnit. Dir.removeFile) extantPaths
{-# INLINEABLE deleteStaleFiles #-}

checkCPPEnv :: (P.Member (P.Embed IO) r, K.LogWithPrefixesLE r) => K.Sem r ()
checkCPPEnv = K.wrapPrefix "checkCPPEnv" $ do
  let ev = "HS_CPP_BINDIR"
  cppBinDirM <- K.liftKnit $ Env.lookupEnv ev
  case cppBinDirM of
    Nothing -> K.logLE K.Diagnostic $ toText ev <> " not set. Using existing path for C++ tools."
    Just cppBinDir -> do
      let cppBinDirT = toText cppBinDir
      curPath <- K.liftKnit $ Env.getEnv "PATH"
      let curPathT = toText curPath
      if T.isSuffixOf cppBinDirT curPathT || T.isPrefixOf (cppBinDirT <> ":") curPathT || T.isInfixOf (":" <> cppBinDirT <> ":") curPathT
        then K.logLE K.Diagnostic $ "Current path, " <> show curPathT <> " already has " <> cppBinDirT
        else (do
                 K.logLE K.Diagnostic $ "Current path: " <> show curPath <> " does not contain " <> cppBinDirT <> ".  Prepending " <> cppBinDirT <> " to path for C++ tools."
                 K.liftKnit $ Env.setEnv "PATH" (cppBinDir ++ ":" ++ curPath)
             )
{-# INLINEABLE checkCPPEnv #-}

createDirIfNecessary ::
  (P.Member (P.Embed IO) r, K.LogWithPrefixesLE r) =>
  T.Text ->
  K.Sem r ()
createDirIfNecessary dir = K.wrapPrefix "createDirIfNecessary" $ do
  K.logLE (K.Debug 1) $ "Checking if cache path (\"" <> dir <> "\") exists."
  existsB <- P.embed $ Dir.doesDirectoryExist (toString dir)
  if existsB
    then (do
             K.logLE (K.Debug 1) $ "\"" <> dir <> "\" exists."
             return ())
    else (do
             K.logLE K.Diagnostic $
               "Cache directory (\""
               <> dir
               <> "\") not found. Atttempting to create."
             P.embed $
               Dir.createDirectoryIfMissing True (T.unpack dir))
{-# INLINEABLE createDirIfNecessary #-}

checkDir ::
  (P.Member (P.Embed IO) r, K.LogWithPrefixesLE r) =>
  T.Text ->
  P.Sem r (Maybe ())
checkDir dir = K.wrapPrefix "checkDir" $ do
  cwd <- P.embed Dir.getCurrentDirectory
  K.logLE (K.Debug 1) $ "CWD = \"" <> show cwd <> "\""
  K.logLE (K.Debug 1) $ "Checking if cache path (\"" <> dir <> "\") exists."
  existsB <- P.embed $ Dir.doesDirectoryExist (toString dir)
  if existsB
    then (do
             K.logLE (K.Debug 1) $ "\"" <> dir <> "\" exists."
             return $ Just ()
         )
    else (do
             K.logLE (K.Debug 1) $ "\"" <> dir <> "\" is missing."
             return Nothing
         )
{-# INLINEABLE checkDir #-}

data ModelState = New | Same | Updated T.Text deriving stock Show

renameAndWriteIfNotSame :: K.KnitEffects r => SLP.GeneratedQuantities -> SLP.StanProgram -> T.Text -> T.Text -> K.Sem r ModelState
renameAndWriteIfNotSame gq p modelDir modelName' = do
  let fileName d n = T.unpack $ d <> "/" <> n <> ".stan"
      curFile = fileName modelDir modelName'
      findAvailableName modelDir' modelName'' n = do
        let newName = fileName modelDir' (modelName'' <> "_o" <> T.pack (show (n :: Int)))
        newExists <- K.liftKnit $ Dir.doesFileExist newName
        if newExists then findAvailableName modelDir modelName' (n + 1) else return $ T.pack newName
  K.logLE K.Diagnostic "Generating model stan code"
  newModel <- case SLP.programAsText gq p of
    Right x -> pure x
    Left msg -> K.liftKnit $ X.throwIO $ X.userError $ toString msg
--  Say.say $ "new model is\n" <> newModel
  K.logLE K.Diagnostic $ "Checking if file=" <> toText curFile <> " exists."
  exists <- K.liftKnit $ Dir.doesFileExist curFile
  if exists then (do
--    Say.say $ "reading file=" <> toText curFile
                     extant <- K.liftKnit $ T.readFile curFile
--    Say.say $ "read file=" <> toText curFile
                     if extant == newModel
                       then K.logLE K.Diagnostic ("model file:" <> toText curFile <> " exists and is identical to model.") >> return Same
                       else (do
                                K.logLE K.Diagnostic $ "model file:" <> T.pack curFile <> " exists and is different. Renaming and writing new model to file."
                                newName <- findAvailableName modelDir modelName' 1
                                K.liftKnit $ Dir.renameFile (fileName modelDir modelName') (T.unpack newName)
                                K.liftKnit $ T.writeFile (fileName modelDir modelName') newModel
                                pure $ Updated newName
                            )
                 )
    else (do
             K.logLE K.Diagnostic $ "model file:" <> T.pack curFile <> " doesn't exist.  Writing new."
             K.liftKnit $ T.writeFile (fileName modelDir modelName') newModel
             K.logLE K.Diagnostic $ "model file:" <> T.pack curFile <> " written."
             pure New
         )
