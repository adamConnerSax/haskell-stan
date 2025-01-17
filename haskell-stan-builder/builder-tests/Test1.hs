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
import qualified Stan.Builder.TestUtils as SBT

import qualified Data.Aeson as A
import qualified Data.Text as T

main :: IO ()
main = SBT.testBuild modelData () stanBuilder

data LetterCode = A | B | C deriving stock (Show, Eq, Ord, Enum, Bounded)

data Row = Row { rowId :: Text, letterCode :: LetterCode, count :: Int, val1 :: Double, val2 :: Double}

newtype ModelData = ModelData { rows :: [Row]}

-- set up source type family
-- One source each for ModelData and GQData
type instance SB.DataSource SB.ModelDataT = ModelData
type instance SB.DataSource SB.GQDataT = ()

modelData :: ModelData
modelData = ModelData [Row "a1" A 12 1.1 1.2
                      , Row "a2" A 5 0.8 2.1
                      , Row "b1" B 7 0.7 1.1
                      ]

stanBuilder :: SB.StanBuilderEff ()
stanBuilder = do
  modelDataT <- SB.addData "D1" SB.ModelData (SB.ToFoldable rows)
  letterGroupT <- SB.addEnumGroup @LetterCode "LC"
  SB.addGroupIndexForData letterGroupT modelDataT (SB.makeIndexByCounting show letterCode)
  SB.addGroupIntMapForData letterGroupT modelDataT (SB.dataToIntMapFromEnum letterCode)
  muP <- SB.simpleParameter (SL.NamedDeclSpec "mu" SL.realSpec)
         (SB.given (SL.realE 1) SL.:> SB.given (SL.realE 0) SL.:> SL.TNil)
         (SL.simpleDensity "normal")

  pure ()
