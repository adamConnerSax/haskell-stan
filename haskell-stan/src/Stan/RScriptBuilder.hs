{-# LANGUAGE CPP #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module Stan.RScriptBuilder
  (
    module Stan.RScriptBuilder
  )
where


import qualified Stan.ModelConfig as SC

import qualified Colonnade as Col
import qualified Control.Foldl as Foldl
import qualified Data.Map as M
import qualified Data.Text as T
import qualified Frames as F
import qualified Frames.Streamly.CSV as FStreamly
import qualified Frames.Streamly.InCore as FStreamly
import Frames.Streamly.Streaming.Streamly (StreamlyStream(..))
import qualified System.Process as Process
#if MIN_VERSION_streamly(0,9,0)
import qualified Streamly.Data.Stream as Streamly
#else
import qualified Streamly.Prelude as Streamly
#endif
import qualified Text.Printf as Printf
import qualified Knit.Report as K

#if MIN_VERSION_streamly(0,9,0)
type Stream = Streamly.Stream
#else
type Stream = Streamly.SerialT
#endif

type StreamlyS = StreamlyStream Stream

libsForShinyStan :: [Text]
libsForShinyStan = ["rstan", "shinystan", "rjson"]

libsForPPC :: [Text]
libsForPPC = ["rstan", "rjson", "bayesplot"]

libsForLoo :: [Text]
libsForLoo = ["rstan", "shinystan", "loo", "bayesplot"]

addLibs :: [T.Text] -> T.Text
addLibs = foldMap addOneLib where
  addOneLib t = "library(" <> t <> ")\n"

rArray :: (a -> T.Text) -> [a] -> T.Text
rArray asText as = "c(" <> T.intercalate "," (fmap asText as) <> ")"

{-
rSetWorkingDirectory :: SC.ModelRunnerConfig -> T.Text -> IO T.Text
rSetWorkingDirectory config dirBase = do
  let wd = dirBase <> "/" <> SC.mrcModelDir config
  cwd <- T.pack <$> Dir.canonicalizePath (T.unpack wd)
  return $ "setwd(\"" <> cwd <> "\")"
-}

rReadStanCSV :: SC.ModelRun -> SC.ModelRunnerConfig -> T.Text -> Text
rReadStanCSV mr config fitName = fitName <> " <- read_stan_csv(" <> rArray (\x -> "\"" <> toText x <> "\"") (SC.finalSamplesFileNames mr config) <> ")"

rStanModel :: SC.ModelRun -> SC.ModelRunnerConfig -> T.Text
rStanModel mr config =
  let rin = SC.mrcInputNames config
      in "stan_model(" <> SC.rinModelDir rin <> "/" <> SC.modelFileName mr rin <> ")"

llName :: Text -> Text
llName = ("ll_" <>)

reName :: Text -> Text
reName = ("re_" <>)

rExtractLogLikelihood :: T.Text -> T.Text
rExtractLogLikelihood fitName = "extract_log_lik(" <> fitName <> ", merge_chains = FALSE)"

rPSIS :: T.Text -> Int -> T.Text
rPSIS fitName nCores = "psis(" <> llName fitName <> ", r_eff=" <> reName fitName <> ", cores=" <> show nCores <> ")"

rExtract :: T.Text -> T.Text
rExtract fitName = "rstan::extract(" <> fitName <> ")"

rReadJSON :: SC.ModelRunnerConfig -> T.Text
rReadJSON config =
  let modelDir = SC.mrcModelDir config
      dataFilePrefix = SC.rinData $ SC.mrcInputNames config
  in "jsonData_" <> dataFilePrefix <> " <- fromJSON(file = \"" <> modelDir <> "/data/" <> SC.modelDataFileName (SC.mrcInputNames config) <> "\")"

rMessage :: T.Text -> T.Text
rMessage t = "sink(stderr())\n" <> rPrint t <> "\nsink()\n"

rMessageText :: T.Text -> T.Text
rMessageText t = rMessage $ "\"" <> t <> "\""

rPrint :: T.Text -> T.Text
rPrint t = "print(" <> t <> ")"

rPrintText :: T.Text -> T.Text
rPrintText t = rPrint $ "\"" <> t <> "\""

-- Named version is simpler if you just need to copy a value from jsonData into global namespace
-- Expr version lets you run R code to build the value to put in global namespace
data UnwrapJSON = UnwrapNamed T.Text T.Text | UnwrapExpr T.Text T.Text deriving stock (Show, Eq, Ord)

unwrap :: Text -> UnwrapJSON -> T.Text
unwrap n (UnwrapNamed jn rn) = rn <> " <- jsonData_" <> n <> " $ " <> jn <> "\n"
unwrap _ (UnwrapExpr je rn) = rn <> " <- " <> je <> "\n"

unwrapCode :: SC.ModelRunnerConfig -> [UnwrapJSON] -> T.Text
unwrapCode config unwrapJSONs =
  if null unwrapJSONs
  then ""
  else
    let rin = SC.mrcInputNames config
        n = SC.rinData rin
        unwraps = mconcat $ fmap (unwrap n) unwrapJSONs
    in rReadJSON config
       <> "\n"
       <> unwraps

shinyStanScript :: SC.ModelRun -> SC.ModelRunnerConfig -> [UnwrapJSON] -> T.Text
shinyStanScript mr config unwrapJSONs =
  let rin = SC.mrcInputNames config
      fitName = "stanfit_" <> SC.rinModel rin <> "_" <> SC.rinData rin
      readStanCSV = rReadStanCSV mr config fitName
      samplesName =  "shiny_samples_" <> fitName
      rScript = addLibs libsForShinyStan
                <> "\n"
                <> rMessageText "Loading csv output.  Might take a minute or two..." <> "\n"
                <> readStanCSV <> "\n"
                <> unwrapCode config unwrapJSONs
                <> rMessageText ("Extracting samples into " <> samplesName) <> "\n"
                <> samplesName <> " <- " <> rExtract fitName <> "\n"

--                <> "stanfit@stanModel <- " <> rStanModel config
                <> rMessageText "Launching shinystan...." <> "\n"
                <> "launch_shinystan(" <> fitName <> ")\n"
  in rScript

looOne :: SC.ModelRun -> SC.ModelRunnerConfig -> Text -> Maybe Text -> Int -> Text
looOne mr config fitName mLooName nCores =
  let readStanCSV = rReadStanCSV mr config fitName
      psisName = "psis_" <> fitName
      looName = fromMaybe ("loo_" <> fitName) mLooName
      samplesName = "ll_samples_" <> fitName
      rScript =  rMessageText ("Loading csv output for " <> fitName <> ".  Might take a minute or two...") <> "\n"
                 <> readStanCSV <> "\n"
                 <> rMessageText "Extracting log likelihood for loo..." <> "\n"
                 <> llName fitName <> " <-" <> rExtractLogLikelihood fitName <> "\n"
                 <> rMessageText "Computing r_eff for loo..." <> "\n"
                 <> reName fitName <> " <- relative_eff(exp(" <> llName fitName <> "), cores = " <> show nCores <> ")\n"
                 <> rMessageText "Computing loo.." <> "\n"
                 <> looName <> " <- loo(" <> llName fitName <> ", r_eff=" <> reName fitName <> ", cores=" <> show nCores <> ", save_psis=TRUE)\n"
                 <> rMessage looName <> "\n"
                 <> rMessageText "Computing PSIS..."
                 <> psisName <> " <- " <> looName <> "$psis_object" <> "\n"
                 <> rMessageText ("Placing samples in " <> samplesName) <> "\n"
                 <> samplesName <> " <- " <> rExtract fitName <> "\n"
                 <> rMessageText ("E.g., 'ppc_loo_pit_qq(yXXX_" <> fitName <> ", as.matrix(" <> samplesName <> "$y_ppred), weights(" <> psisName <> "))'") <> "\n"
  in rScript

looScript ::  SC.ModelRun -> SC.ModelRunnerConfig -> Maybe T.Text-> Int -> T.Text
looScript mr config mLooName nCores =
  let rin = SC.mrcInputNames config
      fitName = "stanfit_" <> SC.rinModel rin <> "_" <> SC.rinData rin
      justLoo = looOne mr config fitName mLooName nCores
  in addLibs libsForLoo <> justLoo

{-
ppcScript :: SC.ModelRun -> SC.ModelRunnerConfig -> [UnwrapJSON] -> T.Text
ppcScript mr config unwrapJSONs =
  let readSTanCSV = rReadStanCSV mr config "stanfit"
      rScript = addLibs libsForPPC
        <> "\n"
        <> rMessageText "Loading csv output.  Might take a minute or two..." <> "\n"
        <> readStanCSV <> "\n"
        <> unwrapCode config unwrapJSONs
        <> rMessageText "Making PPC charts..."
        <> "ppc_parms <- extract(stanfit)"
-}

compareScript ::  Foldable f
              => SC.ModelRun -> f SC.ModelRunnerConfig -> Int -> Maybe Text -> Text
compareScript mr configs nCores mOutCSV =
  let  doOne (n, c) = looOne mr c (SC.outputPrefix mr $ SC.mrcInputNames c) (Just $ "model" <> show (n :: Int)) nCores
       (numModels, configList) = Foldl.fold ((,) <$> Foldl.length <*> Foldl.list) configs
       tCompare = "c <- loo_compare(" <> T.intercalate "," (("model" <>) . show <$> [1..numModels]) <> ")\n"
       writeTable = rMessage "c,simplify=FALSE" <> "\n"
       writeCSV = "write.csv(c" <> maybe ")\n" (\csvName -> "," <> csvName <> ")\n") mOutCSV
       looScripts = mconcat $ fmap doOne  $ zip [1..] configList
       rScript = addLibs libsForLoo <> looScripts  <> tCompare <> writeTable <> writeCSV
  in rScript

-- The below requires Frames and thus adds a dependency

type Model = "Model" F.:-> Text
type ELPD_Diff = "elpd_diff" F.:-> Double
type SE_Diff = "se_diff" F.:-> Double
type ELPD_Loo = "elpd_loo" F.:-> Double
type SE_ELPD_Loo = "se_elpd_loo" F.:-> Double
type P_Loo = "p_loo" F.:-> Double
type SE_P_Loo = "se_p_loo" F.:-> Double
type LOOIC = "looic" F.:-> Double
type SE_LOOIC = "se_looic" F.:-> Double

type LOO_DataR = [ELPD_Diff, SE_Diff, ELPD_Loo, SE_ELPD_Loo, P_Loo, SE_P_Loo, LOOIC, SE_LOOIC]
type LOO_R = Model : LOO_DataR

compareModels :: forall st cd r f. (SC.KnitStan st cd r, Traversable f)
              => SC.ModelRun -> f (Text, SC.ModelRunnerConfig) -> Int -> K.Sem r (F.FrameRec LOO_R)
compareModels mr configs nCores = do
  let script = compareScript mr (snd <$> configs) nCores Nothing
  let cp = Process.proc "R" ["BATCH", "--no-save", "--no-restore"]
  K.liftKnit  @IO $ putTextLn "Running R for loo comparisons..."
  rOut <- toText <$> (K.liftKnit $ Process.readCreateProcess cp (toString script))
  putTextLn "R finished."
  let sRText = Streamly.filter (not . T.isPrefixOf ">") $ Streamly.fromList $ lines rOut
  fLooRaw :: F.FrameRec LOO_R <- K.liftKnit @IO
                                 $ FStreamly.inCoreAoS @_ @_ @StreamlyS
                                 $ FStreamly.streamTable
                                 $ StreamlyStream
#if MIN_VERSION_streamly(0,9,0)
                                 $ fmap (T.split (== ','))
#else
                                 $ Streamly.map (T.split (== ','))
#endif
                                 $ Streamly.drop 1 sRText
  -- map results to models
  let resultModelMap :: Map Text Text = M.fromList $ zip ((\n -> "model" <> show (n :: Int)) <$> [1..]) (Foldl.fold (Foldl.premap fst Foldl.list) configs)
      fixName :: F.Record LOO_R -> F.Record LOO_R
      fixName r =
        let oldName = F.rgetField @Model r
            newName = fromMaybe oldName $ M.lookup oldName resultModelMap
        in F.rputField @Model newName r
  return $ fmap fixName fLooRaw

--  let nameFrame = F.toFrame $ fmap (F.&: V.RNil) $ fst <$> configs
--      fLoo :: F.FrameRec LOO_R = nameFrame `F.zipFrames` (F.rcast @LOO_DataR <$> fLooRaw)

looTextColonnade :: Int -> Col.Colonnade Col.Headed (F.Record LOO_R) Text
looTextColonnade digits =
  let printDouble = toText @String . Printf.printf "%.*f" digits
  in mconcat
     [
       Col.headed "Model" (F.rgetField @Model)
     , Col.headed "elpd diff" (printDouble . F.rgetField @ELPD_Diff)
     , Col.headed "se diff" (printDouble . F.rgetField @SE_Diff)
     , Col.headed "elpd loo" (printDouble . F.rgetField @ELPD_Loo)
     , Col.headed "se_elpd_loo" (printDouble . F.rgetField @SE_ELPD_Loo)
     , Col.headed "p_loo" (printDouble . F.rgetField @P_Loo)
     , Col.headed "se_p_loo" (printDouble . F.rgetField @SE_P_Loo)
     ]
