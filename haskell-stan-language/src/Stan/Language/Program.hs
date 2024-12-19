{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Stan.Language.Program (
    module Stan.Language.Program
) where

import Prelude hiding (All)
import qualified Control.Foldl as FL
import Data.Array ((!), (//))
import qualified Data.Array as Array
import qualified Stan.Language.Statements as SLS
import qualified Stan.Language.Evaluate as SLE

import qualified Prettyprinter.Render.Text as PP
import qualified Prettyprinter as PP

-- TODO
-- 1. Make GQ Block one constructor with a Label
--   data GQSection = GQLL | GQPP | GQOther Text
--   and then data StanBlock = ...
--                           | SBGeneratedQuantities GQSection

-- Various stock Generated Quantities sections
-- Should these be something we can define on the fly?
data GeneratedQuantities = NoGQ
                         | NeitherLL_PP
                         | OnlyLL
                         | OnlyPP
                         | All deriving stock (Show, Eq)

-- sections of a stan program.
-- We should make the GQ section one section with a set of possibilities rather than separate sections
data StanBlock = SBFunctions
               | SBData
               | SBDataGQ
               | SBTransformedData
               | SBTransformedDataGQ
               | SBParameters
               | SBTransformedParameters
               | SBModel
               | SBGeneratedQuantities
               | SBLogLikelihood
               | SBPosteriorPrediction
               deriving stock (Show, Eq, Ord, Enum, Bounded, Array.Ix)

-- the StanBlock type has more sections so we can selectively add and remove things which are for
-- only generated quantitied or the generation of log-likelihoods
newtype StanProgram = StanProgram {unStanProgram :: Array.Array StanBlock [SLS.UStmt]}

-- combine two programs, one above the other *in each block*
instance Semigroup StanProgram where
  (StanProgram a1) <> (StanProgram a2)
    = StanProgram $ Array.listArray (minBound, maxBound) $ zipWith (<>) (Array.elems a1) (Array.elems a2)

emptyStanProgram :: StanProgram
emptyStanProgram = StanProgram $ Array.listArray (minBound, maxBound) $ repeat []

programHasLLBlock :: StanProgram -> Bool
programHasLLBlock p = not $ null (unStanProgram p Array.! SBLogLikelihood)

programHasPPBlock :: StanProgram -> Bool
programHasPPBlock p = not $ null (unStanProgram p Array.! SBPosteriorPrediction)

-- this is...precarious.  No way to check that we are using all of the array
programToStmt :: GeneratedQuantities -> StanProgram -> SLS.UStmt
programToStmt gq p = SLS.SGroup SLS.UnScoped fullProgramStmt
  where
    stmtsArray = unStanProgram p
    fullProgramStmt  =
      let (s, ss1) = let d = dataStmt in maybe (d, []) (\x -> (x, [d])) functionsStmtM
          ss2 = ss1 ++ maybe [] pure tDataStmtM
          ss3 = ss2 ++ [paramsStmt]
          ss4 = ss3 ++ maybe [] pure tParamsStmtM
          ss5 = ss4 ++ [modelStmt]
          ss6 = ss5 ++ maybe [] pure gqStmtM
      in s :| ss6
    functionsStmtM = let x = stmtsArray ! SBFunctions in if null x then Nothing else Just (SLS.SBlock SLS.FunctionsStmts $ SLS.grouped SLS.UnScoped x)
    dataStmt =
        let d = stmtsArray ! SBData
            gqd = SLS.comment ("For Generated Quantities" :| []) : stmtsArray ! SBDataGQ
         in SLS.SBlock SLS.DataStmts $ SLS.grouped SLS.UnScoped (d ++ if gq `elem` [NeitherLL_PP, All] then gqd else [])
    tDataStmtM =
      let
        x = stmtsArray ! SBTransformedData
        xGQ = if  not (null $ stmtsArray ! SBTransformedDataGQ)
              then SLS.comment ("For Generated Quantities" :| []) : stmtsArray ! SBTransformedDataGQ
              else stmtsArray ! SBTransformedDataGQ
      in if null x && null xGQ then Nothing else Just (SLS.SBlock SLS.TDataStmts $ SLS.grouped SLS.UnScoped $ x ++ if gq `elem` [NeitherLL_PP, All] then xGQ else [])
    paramsStmt = SLS.SBlock SLS.ParametersStmts $ SLS.grouped SLS.UnScoped $ stmtsArray ! SBParameters
    tParamsStmtM = let x = stmtsArray ! SBTransformedParameters in if null x then Nothing else Just (SLS.SBlock SLS.TParametersStmts $ SLS.grouped SLS.UnScoped x)
    modelStmt = SLS.SBlock SLS.ModelStmts $ SLS.grouped SLS.UnScoped $ stmtsArray ! SBModel
    gqStmtM =
        let gqs = stmtsArray ! SBGeneratedQuantities
            lls = stmtsArray ! SBLogLikelihood
            pps = stmtsArray ! SBPosteriorPrediction
         in case gq of
                NoGQ -> Nothing
                NeitherLL_PP -> Just $ SLS.SBlock SLS.GeneratedQuantitiesStmts $ SLS.grouped SLS.UnScoped gqs
                OnlyLL -> Just $ SLS.SBlock SLS.GeneratedQuantitiesStmts $ SLS.grouped SLS.UnScoped lls
                OnlyPP -> Just $ SLS.SBlock SLS.GeneratedQuantitiesStmts $ SLS.grouped SLS.UnScoped pps
                All -> Just $ SLS.SBlock SLS.GeneratedQuantitiesStmts $ SLS.grouped SLS.UnScoped $ gqs ++ lls ++ pps


-- check if the type of statement is allowed in the block then, if so, provide the modification function
-- otherwise error
addStmtToBlock' :: ([SLS.UStmt] -> SLS.UStmt -> [SLS.UStmt]) -> StanBlock -> SLS.UStmt -> Either Text (StanProgram -> StanProgram)
addStmtToBlock' addF sb s = do
  let f sp =
        let p = unStanProgram sp
        in StanProgram $ p // [(sb, p ! sb `addF` s)]
  case s of
    SLS.SFunction {} -> if sb == SBFunctions
                       then Right f
                       else Left "Functions and only functions can appear in the function block."
    _ -> if sb `elem` [SBData, SBDataGQ, SBParameters]
      then case s of
             SLS.SDeclare {} -> Right f
             SLS.SComment {} -> Right f
--             SLS.SPrint {} -> Right f
--             SLS.SReject {} -> Right f
             _ -> Left $ "Statement other than declaration or comment in data or parameters block: \n"
               <> (case stmtAsText s of
                     Left err -> "Error trying to render statement (" <> err <> ")"
                     Right st -> st)
      else Right f

addStmtToBlock :: StanBlock -> SLS.UStmt -> Either Text (StanProgram -> StanProgram)
addStmtToBlock = addStmtToBlock' (\stmts s -> stmts ++ [s])

addStmtToBlockTop :: StanBlock -> SLS.UStmt -> Either Text (StanProgram -> StanProgram)
addStmtToBlockTop = addStmtToBlock' $ flip (:)

addStmtsToBlock :: Traversable f => StanBlock -> f SLS.UStmt -> Either Text (StanProgram -> StanProgram)
addStmtsToBlock b stmts = do
  fs <- traverse (addStmtToBlock b) stmts
  let g sp = foldl' (\sp' f -> f sp') sp fs
  return g

addStmtsToBlockTop :: Traversable f => StanBlock -> f SLS.UStmt -> Either Text (StanProgram -> StanProgram)
addStmtsToBlockTop b stmts = do
  fs <- traverse (addStmtToBlockTop b) $ reverse $ FL.fold FL.list stmts
  let g sp = foldl' (\sp' f -> f sp') sp fs
  return g

programAsText :: GeneratedQuantities -> StanProgram -> Either Text Text
programAsText gq p = stmtAsText $ programToStmt gq p

stmtAsText :: SLS.UStmt -> Either Text Text
stmtAsText = stmtAsText' PP.defaultLayoutOptions

stmtAsText' :: PP.LayoutOptions -> SLS.UStmt -> Either Text Text
stmtAsText' lo stmt = case SLE.statementToCodeE SLS.emptyLookupCtxt stmt of
  Right x -> pure $ PP.renderStrict $ PP.layoutSmart lo x
  Left err ->
    let msg = "Lookup error when building code from tree: " <> err <> "\n"
              <> "Tree with failed lookups between hashes follows.\n"
              <> case SLE.eStatementToCodeE SLS.emptyLookupCtxt stmt of
                   Left err2 -> "Yikes! Can't build error tree: " <> err2 <> "\n"
                   Right x -> PP.renderStrict $ PP.layoutSmart lo x
    in Left msg
