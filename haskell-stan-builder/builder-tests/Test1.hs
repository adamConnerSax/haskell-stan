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

main :: IO ()
main = do
  let sb' = do
        stanBuilder
        modelJSONF <- SB.buildJSONFromDataM @ModelData
        gqJSONF <- SB.buildJSONFromDataM @()
        pure (modelJSONF, gqJSONF)
--        modelIntMapsBuilder <- SB.
  case SB.runStanBuilderDAG modelData () sb' of
    Left err -> putTextLn $ "Error in runStanBuilder: " <> err
    Right (SB.BuilderState _ _ _ _ _ _ (SB.StanCode _ sp), (modelJSF, gqJSF)) -> do
      case SL.programAsText SL.All sp of
        Left err -> putTextLn $ "Error during AST -> Text: " <> err
        Right code -> putTextLn code
      putTextLn $ "model JSON: "
      putTextLn $ show $ fmap A.pairs $ modelJSF modelData

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
