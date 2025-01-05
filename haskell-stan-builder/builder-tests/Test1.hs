{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications     #-}

module Main where

import qualified Stan.Language as SL
import qualified Stan.Functions as SF
import Stan.Functions.Operators
import qualified Stan.Builder as SB


main :: IO ()
main = do
  case SB.runStanBuilder modelData () groupBuilder stanBuilder of
    Left err -> putTextLn $ "Error in runStanBuilder: " <> err
    Right (SB.BuilderState _ _ _ _ _ _ _ _ (SB.StanCode _ sp), _) -> do
      case SL.programAsText SL.All sp of
        Left err -> putTextLn $ "Error during AST -> Text: " <> err
        Right code -> putTextLn code

modelData :: ()
modelData = ()

groupBuilder :: SB.StanGroupBuilderM () () ()
groupBuilder = pure ()

stanBuilder :: SB.StanBuilderM () () ()
stanBuilder = do
  SB.setBlock SL.SBData
  SB.addStmtToCode $ SL.cwStmt_ $ do
    x <- SL.declareW "x" SL.intSpec
    pure ()
