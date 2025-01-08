{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies     #-}

module Main where

import qualified Stan.Language as SL
import qualified Stan.Functions as SF
import Stan.Functions.Operators
import qualified Stan.Builder as SB

import qualified Data.Aeson as A
import qualified Data.Text as T

main :: IO ()
main = do
{-  let sb' = do
        stanBuilder
--        modelJSONF <- SB.buildJSONFromDataM @ModelData
--        gqJSONF <- SB.buildJSONFromDataM @()
--        pure (modelJSONF, gqJSONF)
--        modelIntMapsBuilder <- SB.
-}
  case SB.runStanBuilderDAG modelData () stanBuilder of
    Left err -> putTextLn $ "Error in runStanBuilder: " <> err
    Right (bs, logs, ()) -> do
      let SB.StanCode _ sp = SB.code bs
          modelJsonE = SB.modelJsonE bs modelData
          gqJsonE = SB.gqJsonE bs ()
          modelIntMaps = SB.intMapsFromRowInfos (SB.modelRowBuilders bs) modelData
          gqIntMaps = SB.intMapsFromRowInfos (SB.gqRowBuilders bs) ()
      putTextLn $ "messages: "
      putTextLn $ T.intercalate "\n" logs
      case SL.programAsText SL.All sp of
        Left err -> putTextLn $ "Error during AST -> Text: " <> err
        Right code -> putTextLn code
      putTextLn $ "model JSON: "
      putTextLn $ show $ fmap A.pairs $ modelJsonE
      putTextLn $ "model Group IntMaps:"
      putTextLn $ show $ fmap SB.displayDataSetGroupIntMaps $ modelIntMaps

data LetterCode = A | B | C deriving stock (Show, Eq, Ord, Enum, Bounded)

data Row = Row { rowId :: Text, letterCode :: LetterCode, count :: Int, val1 :: Double, val2 :: Double}

data ModelData = ModelData { rows :: [Row]}

type instance SB.DataSource Row = ModelData
type instance SB.SourceType SB.ModelDataT = ModelData
type instance SB.SourceType SB.GQDataT = ()

modelData :: ModelData
modelData = ModelData [Row "a1" A 12 1.1 1.2
                      , Row "a2" A 5 0.8 2.1
                      ]

stanBuilder :: SB.StanBuilderEff ModelData () ()
stanBuilder = do
  modelDataT <- SB.addData modelData "D1" SB.ModelData (SB.ToFoldable rows)
  letterGroupT <- SB.addEnumGroup @LetterCode "LC"
  SB.addGroupIndexForData letterGroupT modelDataT (SB.makeIndexByCounting show letterCode)
  SB.addGroupIntMapForData letterGroupT modelDataT (SB.dataToIntMapFromEnum letterCode)
  muP <- SB.simpleParameter (SL.NamedDeclSpec "mu" SL.realSpec)
         (SB.given (SL.realE 1) SL.:> SB.given (SL.realE 0) SL.:> SL.TNil)
         (SL.simpleDensity "normal")
  pure ()
