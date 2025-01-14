{-# LANGUAGE DataKinds #-}
module Stan.Builder.TestUtils
  (
    module Stan.Builder.TestUtils
  )
  where

import qualified Stan.Language as SL
import qualified Stan.Builder as SB

import qualified Data.Aeson as A
import qualified Data.Text as T

testBuild :: SB.DataSource SB.ModelDataT
          -> SB.DataSource SB.GQDataT
          ->  SB.StanBuilderEff (SB.DataSource SB.ModelDataT) (SB.DataSource SB.GQDataT) () -> IO ()
testBuild md gq stanBuilder = do
  case SB.runStanBuilderDAG md gq stanBuilder of
    Left err -> putTextLn $ "Error in runStanBuilder: " <> err
    Right (bs, logs, ()) -> do
      let SB.StanCode _ sp = SB.code bs
          modelJsonE = SB.modelJsonE bs md
          gqJsonE = SB.gqJsonE bs gq
          modelIntMaps = SB.intMapsFromRowInfos (SB.modelRowBuilders bs) md
          gqIntMaps = SB.intMapsFromRowInfos (SB.gqRowBuilders bs) gq
      putTextLn $ "messages: "
      putTextLn $ T.intercalate "\n" logs
      case SL.programAsText SL.All sp of
        Left err -> putTextLn $ "Error during AST -> Text: " <> err
        Right code -> putTextLn code
      putTextLn $ "model JSON: "
      putTextLn $ show $ fmap A.pairs $ modelJsonE
      putTextLn $ "GQ JSON: "
      putTextLn $ show $ fmap A.pairs $ gqJsonE
      putTextLn $ "model Group IntMaps:"
      putTextLn $ show $ fmap SB.displayDataSetGroupIntMaps $ modelIntMaps
      putTextLn $ "GQ Group IntMaps:"
      putTextLn $ show $ fmap SB.displayDataSetGroupIntMaps $ gqIntMaps
