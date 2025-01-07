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


main :: IO ()
main = do
  case SB.runStanBuilderDAG modelData () stanBuilder of
    Left err -> putTextLn $ "Error in runStanBuilder: " <> err
    Right (SB.BuilderState _ _ _ _ _ _ (SB.StanCode _ sp), _) -> do
      case SL.programAsText SL.All sp of
        Left err -> putTextLn $ "Error during AST -> Text: " <> err
        Right code -> putTextLn code

data LetterCode = A | B | C deriving stock (Show, Eq, Ord, Enum, Bounded)

data Row = Row { rowId :: Text, letterCode :: LetterCode, count :: Int, val1 :: Double, val2 :: Double}

type instance SB.DataSource Row = ModelData

data ModelData = ModelData { rows :: [Row]}

modelData :: ModelData
modelData = ModelData [Row "a1" A 12 1.1 1.2
                      , Row "a2" A 5 0.8 2.1
                      ]

stanBuilder :: SB.StanBuilderEff ModelData () ()
stanBuilder = do
  modelData <- SB.addData modelData "D1" SB.ModelData (SB.ToFoldable rows)
  let letterGroup = SB.GroupTypeTag @LetterCode "LetterCode"
  SB.addGroupIndexForData letterGroup modelData (SB.makeIndexByCounting show letterCode)
  SB.addGroupIntMapForData letterGroup modelData (SB.dataToIntMapFromEnum letterCode)

  SB.setBlock SL.SBData
  SB.addStmtToCode $ SL.cwStmt_ $ do
    x <- SL.declareW "x" SL.intSpec
    pure ()
