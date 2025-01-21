{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
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

import qualified Stan.Language.ASTContext as SLA
import qualified Stan.Language.Statement as SLS
import qualified Stan.Language.Statements as SLSS
import qualified Stan.Language.Evaluate as SLE
import qualified Stan.Language.Recursion as SLR

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
programToStmt gq p = SLSS.grouped fullProgramStmt
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
    functionsStmtM = let x = stmtsArray ! SBFunctions in if null x then Nothing else Just (SLSS.block SLS.FunctionsStmts $ SLSS.grouped x)
    dataStmt =
        let d = stmtsArray ! SBData
            gqd = SLSS.comment ("For Generated Quantities" :| []) : stmtsArray ! SBDataGQ
         in SLSS.block SLS.DataStmts $ SLSS.grouped (d ++ if gq `elem` [NeitherLL_PP, All] then gqd else [])
    tDataStmtM =
      let
        x = stmtsArray ! SBTransformedData
        xGQ = if  not (null $ stmtsArray ! SBTransformedDataGQ)
              then SLSS.comment ("For Generated Quantities" :| []) : stmtsArray ! SBTransformedDataGQ
              else stmtsArray ! SBTransformedDataGQ
      in if null x && null xGQ then Nothing else Just (SLSS.block SLS.TDataStmts $ SLSS.grouped $ x ++ if gq `elem` [NeitherLL_PP, All] then xGQ else [])
    paramsStmt = SLSS.block SLS.ParametersStmts $ SLSS.grouped $ stmtsArray ! SBParameters
    tParamsStmtM = let x = stmtsArray ! SBTransformedParameters in if null x then Nothing else Just (SLSS.block SLS.TParametersStmts $ SLSS.grouped x)
    modelStmt = SLSS.block SLS.ModelStmts $ SLSS.grouped $ stmtsArray ! SBModel
    gqStmtM =
        let gqs = stmtsArray ! SBGeneratedQuantities
            lls = stmtsArray ! SBLogLikelihood
            pps = stmtsArray ! SBPosteriorPrediction
         in case gq of
                NoGQ -> Nothing
                NeitherLL_PP -> Just $ SLSS.block SLS.GeneratedQuantitiesStmts $ SLSS.grouped gqs
                OnlyLL -> Just $ SLSS.block SLS.GeneratedQuantitiesStmts $ SLSS.grouped lls
                OnlyPP -> Just $ SLSS.block SLS.GeneratedQuantitiesStmts $ SLSS.grouped pps
                All -> Just $ SLSS.block SLS.GeneratedQuantitiesStmts $ SLSS.grouped $ gqs ++ lls ++ pps


-- check if the type of statement is allowed in the block then, if so, provide the modification function
-- otherwise error
addStmtToBlock' :: ([SLS.UStmt] -> SLS.UStmt -> [SLS.UStmt]) -> StanBlock -> SLS.UStmt -> Either Text (StanProgram -> StanProgram)
addStmtToBlock' addF sb s = do
  let f sp =
        let p = unStanProgram sp
        in StanProgram $ p // [(sb, p ! sb `addF` s)]
  _ <- checkStmtBlock sb s
  pure f

checkStmtBlock :: StanBlock -> SLS.UStmt -> Either Text SLS.UStmt
checkStmtBlock sb s = case SLR.unFix s of
  SLS.SFunctionF {} -> if sb == SBFunctions
                       then pure s
                       else Left "Functions and only functions can appear in the function block."
  _ -> if sb `elem` [SBData, SBDataGQ, SBParameters]
       then case SLR.unFix s of
              SLS.SDeclareF {} -> pure s
              SLS.SCommentF {} -> pure s
              SLS.SGroupF SLS.UnBracketed stmts -> SLSS.grouped <$> traverse (checkStmtBlock sb) stmts
              _ ->  Left $ "Statement other than declaration or comment in " <> show sb <> " block: \n"
                    <> (case stmtAsText s of
                          Left err -> "Error trying to render statement (" <> err <> ")"
                          Right st -> st)
       else pure s

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
stmtAsText' lo stmt = case SLE.statementToCodeE SLA.emptyLookupCtxt stmt of
  Right x -> pure $ PP.renderStrict $ PP.layoutSmart lo x
  Left err ->
    let msg = "Lookup error when building code from tree: " <> err <> "\n"
              <> "Tree with failed lookups between hashes follows.\n"
              <> case SLE.eStatementToCodeE SLA.emptyLookupCtxt stmt of
                   Left err2 -> "Yikes! Can't build error tree: " <> err2 <> "\n"
                   Right x -> PP.renderStrict $ PP.layoutSmart lo x
    in Left msg
