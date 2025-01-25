{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

module Stan.Runner.Config
  (
    module Stan.Runner.Config
  )
where

import Stan.Builder as SB

import qualified CmdStan as CS
import qualified CmdStan.Types as CS
import qualified Knit.Report as K
import qualified Data.Aeson as A
import qualified Data.Text as T

data GQNames = GQNames { gqModelName :: Text, gqDataName :: Text} deriving stock (Show, Eq, Ord)

data RunnerInputNames = RunnerInputNames
  { rinModelDir :: Text -- ^ top-level Directory for stan model code & parent of data/script/ouput directories
  , rinModel :: Text -- ^ prefix for model code.
  , rinGQ :: Maybe GQNames  -- ^ If there will be generated quantities, prefix for that model code and data
  , rinData :: Text -- ^ prefix for data files
  }  deriving stock (Show, Ord, Eq)

data ModelRun = MRNoGQ | MROnlyLL | MROnlyPP | MRFull deriving stock (Show, Eq)

-- for merged samples
llSuffix :: Text
llSuffix = "_LL"

modelSuffix :: ModelRun -> RunnerInputNames -> Text
modelSuffix MRNoGQ _ = "_noGQ"
modelSuffix MROnlyLL _ = "_onlyLL"
modelSuffix MROnlyPP _ = "_onlyPP"
modelSuffix MRFull rin = "_" <> fromMaybe "GQ" (gqModelName <$> rinGQ rin)
{-# INLINEABLE modelSuffix #-}

unmergedSamplesSuffix :: ModelRun -> RunnerInputNames -> Text
unmergedSamplesSuffix mr rin = modelSuffix mr rin
{-# INLINEABLE unmergedSamplesSuffix #-}

mergedSamplesSuffix :: ModelRun -> Text
mergedSamplesSuffix MRNoGQ = "_noGQ"
mergedSamplesSuffix MROnlyLL = "_ll"
mergedSamplesSuffix MROnlyPP = "_pp"
mergedSamplesSuffix MRFull = ""
{-# INLINEABLE mergedSamplesSuffix #-}

modelName :: ModelRun -> RunnerInputNames -> Text
modelName mr rin = rinModel rin <> modelSuffix mr rin
{-# INLINEABLE modelName #-}

modelDirPath :: RunnerInputNames -> Text -> FilePath
modelDirPath rin fName = toString $ rinModelDir rin <> "/" <> fName

modelPath :: ModelRun -> RunnerInputNames -> FilePath
modelPath mr rin = modelDirPath rin $ modelName mr rin
{-# INLINEABLE modelPath #-}

subdirPath :: RunnerInputNames -> Text -> Text -> FilePath
subdirPath rin subDirName fName = toString $ rinModelDir rin <> "/" <> subDirName <> "/" <> fName

outputDirPath :: RunnerInputNames -> Text -> FilePath
outputDirPath rin = subdirPath rin "output"

dataDirPath :: RunnerInputNames -> Text -> FilePath
dataDirPath rin = subdirPath rin "data"

rDirPath :: RunnerInputNames -> Text -> FilePath
rDirPath rin = subdirPath rin "R"

data StanMCParameters = StanMCParameters
  { smcNumChains :: Int
  , smcNumThreads :: Int
  , smcNumWarmupM :: Maybe Int
  , smcNumSamplesM :: Maybe Int
  , smcAdaptDeltaM :: Maybe Double
  , smcMaxTreeDepth :: Maybe Int
  , smcRandomSeed :: Maybe Int
  } deriving stock (Show, Eq, Ord)

data StanExeConfigWrapper = MultiThreadedExeConfig CS.StanExeConfig |  SingleThreadedExeConfig (Int -> CS.StanExeConfig)

data ModelRunnerConfig = ModelRunnerConfig
  { mrcDoOnlyLL :: Bool
  , mrcDoOnlyPP :: Bool
  , mrcStanMakeConfig :: ModelRun -> CS.MakeConfig
  , mrcStanSummaryConfig :: CS.StansummaryConfig
  , mrcInputNames :: RunnerInputNames
  , mrcStanMCParameters :: StanMCParameters
  , mrcLogSummary :: Bool
  , mrcRunDiagnose :: Bool
  }

mrcModelDir :: ModelRunnerConfig -> Text
mrcModelDir = rinModelDir . mrcInputNames

modelFileName :: ModelRun -> RunnerInputNames -> Text
modelFileName mr rin = modelName mr rin <> ".stan"

addModelDirectory :: RunnerInputNames -> Text -> Text
addModelDirectory rin x = rinModelDir rin <> "/" <> x

modelDependency :: K.KnitEffects r => ModelRun -> RunnerInputNames -> K.Sem r (K.ActionWithCacheTime r ())
modelDependency mr rin = K.fileDependency (toString modelFile)  where
  modelFile = addModelDirectory rin (modelFileName mr rin)

modelDataFileName :: RunnerInputNames -> Text
modelDataFileName rin = rinData rin <> ".json"

gqDataFileName :: RunnerInputNames -> Maybe Text
gqDataFileName rin = fmap (<> ".json") $ (gqDataName <$> rinGQ rin)

modelDataDependency :: K.KnitEffects r => RunnerInputNames -> K.Sem r (K.ActionWithCacheTime r ())
modelDataDependency rin = K.fileDependency $ (toString $ addModelDirectory rin $ ("data/" <> modelDataFileName rin))

gqDataDependency :: K.KnitEffects r => RunnerInputNames -> K.Sem r (Maybe (K.ActionWithCacheTime r ()))
gqDataDependency rin = case gqDataFileName rin of
  Nothing -> return Nothing
  Just gqName -> do
    dep <- K.fileDependency $ (toString $ addModelDirectory rin $ ("data/" <> gqName))
    return $ Just dep

combinedDataFileName :: RunnerInputNames -> Text
combinedDataFileName rin = rinData rin <> maybe "" ("_" <>) (gqDataName <$> rinGQ rin) <> ".json"


{-
We save separate JSON for model and generated-quantities runs. To run a model with GQ section
we need these combined. Here we check if the combo file is older than either the model data
or the GQ data and, if so, recombine them. Returning a unit action to hold most recent update time
of combined data.
-}
combineData :: K.KnitEffects r => RunnerInputNames -> K.Sem r (K.ActionWithCacheTime r ())
combineData rin = do
  modelDataDep <- modelDataDependency rin
--  gqDataDependencyM <- gqDataDependency rin
  case gqDataFileName rin of
    Nothing -> return modelDataDep
    Just gqName -> do
      let gqFP = dataDirPath rin gqName
      gqDep <- K.fileDependency $ toString $ gqFP
      let comboDeps = (,) <$> modelDataDep <*> gqDep
          comboFP = dataDirPath rin $ combinedDataFileName rin
      comboFileDep <- K.fileDependency comboFP
      K.updateIf comboFileDep comboDeps $ const $ do
          modelDataE <- K.liftKnit $ A.eitherDecodeFileStrict $ dataDirPath rin $ modelDataFileName rin
          modelData <- K.knitEither $ first toText modelDataE
          gqDataE <- K.liftKnit $ A.eitherDecodeFileStrict $ toString gqFP
          gqData <- K.knitEither $ first toText gqDataE
          let combined :: A.Object = modelData <> gqData
          K.liftKnit $ A.encodeFile comboFP combined
          return ()
{-
Action holding most recent update time of model and GQ data (if setup has any)
-}
dataDependency :: K.KnitEffects r => RunnerInputNames -> K.Sem r (K.ActionWithCacheTime r ())
dataDependency rin = do
  modelDataDep <- modelDataDependency rin
  gqDataDepM <- gqDataDependency rin
  case gqDataDepM of
    Nothing -> return modelDataDep
    Just gqDataDep -> return $ const <$> modelDataDep <*> gqDataDep

type KnitStan st cd r = (K.KnitEffects r, K.CacheEffects st cd Text r)

outputPrefix :: ModelRun -> RunnerInputNames -> Text
outputPrefix mr rin = rinModel rin <> "_" <> rinData rin <> gqPart <> unmergedSamplesSuffix mr rin where
  gqName (GQNames mn dn) = mn <> "_" <> dn
  gqPart = if mr == MRFull then maybe "" ("_" <>) $ (gqName <$> rinGQ rin) else ""

mergedPrefix :: ModelRun -> RunnerInputNames -> Text
mergedPrefix mr rin = rinModel rin <> "_" <> rinData rin <> gqPart <> mergedSamplesSuffix mr where
  gqName (GQNames mn dn) = mn <> "_" <> dn
  gqPart = if mr == MRFull then maybe "" ("_" <>) $ (gqName <$> rinGQ rin) else ""

samplesFileNames :: ModelRun -> ModelRunnerConfig -> [FilePath]
samplesFileNames mr config =
  let rin = mrcInputNames config
      numChains = smcNumChains $ mrcStanMCParameters config
  in outputDirPath rin . (\n -> outputPrefix mr rin <> "_" <> show n <> ".csv") <$> [1..numChains]

mergedSamplesFP :: ModelRun -> ModelRunnerConfig -> Int -> FilePath
mergedSamplesFP MRNoGQ _ _ = error "mergedFP: called with MRNoGQ argument!"
mergedSamplesFP mr config n = outputDirPath (mrcInputNames config) $ mergedPrefix mr (mrcInputNames config) <> "_" <> show n <> ".csv"

finalSamplesFileNames :: ModelRun -> ModelRunnerConfig -> [FilePath]
finalSamplesFileNames MRNoGQ config = samplesFileNames MRNoGQ config
finalSamplesFileNames mr config = fmap (mergedSamplesFP mr config) $ [1..(smcNumChains $ mrcStanMCParameters config)]

setSigFigs :: Int -> ModelRunnerConfig -> ModelRunnerConfig
setSigFigs sf mrc = let sc = mrcStanSummaryConfig mrc in mrc { mrcStanSummaryConfig = sc { CS.sigFigs = Just sf } }

noLogOfSummary :: ModelRunnerConfig -> ModelRunnerConfig
cnoLogOfSummary sc = sc { mrcLogSummary = False }

noDiagnose :: ModelRunnerConfig -> ModelRunnerConfig
noDiagnose sc = sc { mrcRunDiagnose = False }

data ConstT (a :: SB.InputDataT) = ConstT

{-
So. DataIndexerType is parameterized by something which takes an SB.InputDataT and returns a Type.
In particular, the type of the DataIndex for this particular setup?
the caching of the index can be different for the model and gq data.
Why can't I just use the unparameterized InputDataT for this?
-}
{- DataIndexerType carries info about whether a particular Data Index exists and, if so, should be cached. -}
data DataIndexerType (b :: SB.InputDataT -> Type) where
  NoIndex :: DataIndexerType ConstT
  TransientIndex :: DataIndexerType b
  CacheableIndex :: (ModelRunnerConfig -> SB.InputDataT -> Text) -> DataIndexerType b

{-
Pattern matching on the first brings the constraint into scope
This allows us to choose not to have the constraint unless we need it.
-}
data Cacheable st b where
  Cacheable :: st (Either Text b) => Cacheable st b
  UnCacheable :: Cacheable st b

data JSONSeries = JSONSeries { modelSeries :: A.Series, gqSeries :: A.Series}

{-
Wrangler represents a function from the Data (model or GQ indexed by 'i') to
an index of type (b i) and a function from the data to the JSON.
Why not just
SB.DataSource i b -> (Either T.Text (b i), Either T.Text A.Series)
or
SB.DataSource i b -> Either T.Text ((b i), A.Series)

??
-}
type Wrangler i b = SB.DataSource i -> (Either T.Text (b i), SB.DataSource i -> Either T.Text A.Series)

{-
unitWrangle :: Wrangler () b
unitWrangle _ = (Left "Wrangle Error. Attempt to build index using a \"Wrangle () _\""
                , const $ Left "Wrangle Error. Attempt to build json using a \"Wrangle () _\""
                )
-}

data DataWrangler (b :: SB.InputDataT -> Type) p where
  Wrangle :: DataIndexerType b
          -> Wrangler SB.ModelDataT b
          -> Maybe (Wrangler SB.GQDataT b)
          -> DataWrangler b ()
  WrangleWithPredictions :: DataIndexerType b
                         -> Wrangler SB.ModelDataT b
                         -> Maybe (Wrangler SB.GQDataT b)
                         -> (Either T.Text (b SB.ModelDataT) -> Either T.Text (b SB.GQDataT) -> p -> Either T.Text A.Series)
                         -> DataWrangler b p

noPredictions :: DataWrangler b p -> DataWrangler b ()
noPredictions w@(Wrangle _ _ _) = w
noPredictions (WrangleWithPredictions x y z _) = Wrangle x y z

dataIndexerType :: DataWrangler b p -> DataIndexerType b
dataIndexerType (Wrangle i _ _) = i
dataIndexerType (WrangleWithPredictions i _ _ _) = i

modelWrangler :: DataWrangler b p -> Wrangler SB.ModelDataT b -- -> (Either T.Text b, a -> Either T.Text JSONSeries)
modelWrangler (Wrangle _ x _) = x
modelWrangler (WrangleWithPredictions _ x _ _) = x

mGQWrangler :: DataWrangler b p -> Maybe (Wrangler SB.GQDataT b)  -- -> (Either T.Text b, a -> Either T.Text JSONSeries)
mGQWrangler (Wrangle _ _ x) = x
mGQWrangler (WrangleWithPredictions _ _ x _) = x

-- produce a result of type b from the data and the model summary
-- NB: the cache time will give you newest of data, indices and stan output
type ResultF r (b :: SB.InputDataT -> Type) p c
  = p
    -> K.ActionWithCacheTime r (SB.DataSource SB.ModelDataT, Either T.Text (b SB.ModelDataT))
    -> Maybe (K.ActionWithCacheTime r (SB.DataSource SB.GQDataT, Either T.Text (b SB.GQDataT)))
    -> K.Sem r c

data ResultAction r (b :: SB.InputDataT -> Type) p c where
  UseSummary :: (CS.StanSummary -> ResultF r b p c) -> ResultAction r b p c
  SkipSummary :: ResultF r b p c -> ResultAction r b p c
  DoNothing :: ResultAction r b p ()

emptyResult :: ResultAction r b p ()
emptyResult = SkipSummary $ \_ _ _ -> pure ()

sampleFile :: T.Text -> Maybe Int -> FilePath
sampleFile outputFilePrefix chainIndexM = toString outputFilePrefix <> (maybe "" (("_" <>) . show) chainIndexM) <> ".csv"

summaryFileName :: ModelRun -> ModelRunnerConfig -> T.Text
summaryFileName mr config = outputPrefix mr (mrcInputNames config) <> "_summary.json"
{-
gqSummaryFileName :: ModelRunnerConfig -> Maybe T.Text
gqSummaryFileName config = fmap (<> "_summary.json") $ gqPrefix (mrcInputNames config)
-}
