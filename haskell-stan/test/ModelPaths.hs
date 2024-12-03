{-# LANGUAGE TemplateHaskell     #-}
module ModelPaths where

import qualified Language.Haskell.TH.Env as Env

dataDir :: FilePath
dataDir = fromMaybe "./" $ fmap toString ($$(Env.envQ "HASKELL_STAN_DIR") :: Maybe String)
