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

module Stan.ModelBuilder.TypedExpressions.Program (
    module Stan.ModelBuilder.TypedExpressions.Program
) where

import qualified Control.Foldl as FL
import Data.Array ((!), (//))
import qualified Data.Array as Array
import qualified Stan.ModelBuilder.BuilderTypes as SBT
import qualified Stan.ModelBuilder.TypedExpressions.Statements as TE
import qualified Stan.ModelBuilder.TypedExpressions.Evaluate as TE

import qualified Prettyprinter.Render.Text as PP
import qualified Prettyprinter as PP


-- the StanBlock type has more sections so we can selectively add and remove things which are for
-- only generated quantitied or the generation of log-likelihoods
newtype StanProgram = StanProgram {unStanProgram :: Array.Array SBT.StanBlock [TE.UStmt]}

-- combine two programs, one above the other *in each block*
instance Semigroup StanProgram where
  (StanProgram a1) <> (StanProgram a2)
    = StanProgram $ Array.listArray (minBound, maxBound) $ zipWith (<>) (Array.elems a1) (Array.elems a2)

emptyStanProgram :: StanProgram
emptyStanProgram = StanProgram $ Array.listArray (minBound, maxBound) $ repeat []

programHasLLBlock :: StanProgram -> Bool
programHasLLBlock p = not $ null (unStanProgram p Array.! SBT.SBLogLikelihood)

programHasPPBlock :: StanProgram -> Bool
programHasPPBlock p = not $ null (unStanProgram p Array.! SBT.SBPosteriorPrediction)

-- this is...precarious.  No way to check that we are using all of the array
programToStmt :: SBT.GeneratedQuantities -> StanProgram -> TE.UStmt
programToStmt gq p = TE.SContext Nothing fullProgramStmt
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
    functionsStmtM = let x = stmtsArray ! SBT.SBFunctions in if null x then Nothing else Just (TE.SBlock TE.FunctionsStmts x)
    dataStmt =
        let d = stmtsArray ! SBT.SBData
            gqd = TE.comment ("For Generated Quantities" :| []) : stmtsArray ! SBT.SBDataGQ
         in TE.SBlock TE.DataStmts (d ++ if gq `elem` [SBT.NeitherLL_PP, SBT.All] then gqd else [])
    tDataStmtM =
      let
        x = stmtsArray ! SBT.SBTransformedData
        xGQ = if  not (null $ stmtsArray ! SBT.SBTransformedDataGQ)
              then TE.comment ("For Generated Quantities" :| []) : stmtsArray ! SBT.SBTransformedDataGQ
              else stmtsArray ! SBT.SBTransformedDataGQ
      in if null x && null xGQ then Nothing else Just (TE.SBlock TE.TDataStmts $ x ++ if gq `elem` [SBT.NeitherLL_PP, SBT.All] then xGQ else [])
    paramsStmt = TE.SBlock TE.ParametersStmts $ stmtsArray ! SBT.SBParameters
    tParamsStmtM = let x = stmtsArray ! SBT.SBTransformedParameters in if null x then Nothing else Just (TE.SBlock TE.TParametersStmts x)
    modelStmt = TE.SBlock TE.ModelStmts $ stmtsArray ! SBT.SBModel
    gqStmtM =
        let gqs = stmtsArray ! SBT.SBGeneratedQuantities
            lls = stmtsArray ! SBT.SBLogLikelihood
            pps = stmtsArray ! SBT.SBPosteriorPrediction
         in case gq of
                SBT.NoGQ -> Nothing
                SBT.NeitherLL_PP -> Just $ TE.SBlock TE.GeneratedQuantitiesStmts gqs
                SBT.OnlyLL -> Just $ TE.SBlock TE.GeneratedQuantitiesStmts lls
                SBT.OnlyPP -> Just $ TE.SBlock TE.GeneratedQuantitiesStmts pps
                SBT.All -> Just $ TE.SBlock TE.GeneratedQuantitiesStmts $ gqs ++ lls ++ pps


-- check if the type of statement is allowed in the block then, if so, provide the modification function
-- otherwise error
addStmtToBlock' :: ([TE.UStmt] -> TE.UStmt -> [TE.UStmt]) -> SBT.StanBlock -> TE.UStmt -> Either Text (StanProgram -> StanProgram)
addStmtToBlock' addF sb s = do
  let f sp =
        let p = unStanProgram sp
        in StanProgram $ p // [(sb, p ! sb `addF` s)]
  case s of
    TE.SFunction {} -> if sb == SBT.SBFunctions
                       then Right f
                       else Left "Functions and only functions can appear in the function block."
    _ -> if sb `elem` [SBT.SBData, SBT.SBDataGQ, SBT.SBParameters]
      then case s of
             TE.SDeclare {} -> Right f
             TE.SComment {} -> Right f
--             TE.SPrint {} -> Right f
--             TE.SReject {} -> Right f
             _ -> Left $ "Statement other than declaration or comment in data or parameters block: \n"
               <> (case stmtAsText s of
                     Left err -> "Error trying to render statement (" <> err <> ")"
                     Right st -> st)
      else Right f

addStmtToBlock :: SBT.StanBlock -> TE.UStmt -> Either Text (StanProgram -> StanProgram)
addStmtToBlock = addStmtToBlock' (\stmts s -> stmts ++ [s])

addStmtToBlockTop :: SBT.StanBlock -> TE.UStmt -> Either Text (StanProgram -> StanProgram)
addStmtToBlockTop = addStmtToBlock' $ flip (:)

addStmtsToBlock :: Traversable f => SBT.StanBlock -> f TE.UStmt -> Either Text (StanProgram -> StanProgram)
addStmtsToBlock b stmts = do
  fs <- traverse (addStmtToBlock b) stmts
  let g sp = foldl' (\sp' f -> f sp') sp fs
  return g

addStmtsToBlockTop :: Traversable f => SBT.StanBlock -> f TE.UStmt -> Either Text (StanProgram -> StanProgram)
addStmtsToBlockTop b stmts = do
  fs <- traverse (addStmtToBlockTop b) $ reverse $ FL.fold FL.list stmts
  let g sp = foldl' (\sp' f -> f sp') sp fs
  return g

programAsText :: SBT.GeneratedQuantities -> StanProgram -> Either Text Text
programAsText gq p = stmtAsText $ programToStmt gq p

stmtAsText :: TE.UStmt -> Either Text Text
stmtAsText = stmtAsText' PP.defaultLayoutOptions

stmtAsText' :: PP.LayoutOptions -> TE.UStmt -> Either Text Text
stmtAsText' lo stmt = case TE.statementToCodeE TE.emptyLookupCtxt stmt of
  Right x -> pure $ PP.renderStrict $ PP.layoutSmart lo x
  Left err ->
    let msg = "Lookup error when building code from tree: " <> err <> "\n"
              <> "Tree with failed lookups between hashes follows.\n"
              <> case TE.eStatementToCodeE TE.emptyLookupCtxt stmt of
                   Left err2 -> "Yikes! Can't build error tree: " <> err2 <> "\n"
                   Right x -> PP.renderStrict $ PP.layoutSmart lo x
    in Left msg
