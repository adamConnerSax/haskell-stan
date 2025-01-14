{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use for_" #-}
{-# HLINT ignore "Use camelCase" #-}

module Stan.BuildingBlocks.Misc
  (
    module Stan.BuildingBlocks.Misc
  )
where

import Prelude hiding (sum, All)

import qualified Stan.Language as SL
import qualified Stan.Language.Statement as SL
import Stan.Language (TypedList(..))
import Stan.Language.Recursion (hfmap)
import qualified Stan.Functions as SF
import Stan.Functions.Operators
import qualified Stan.Builder as SB
import qualified Stan.BuildingBlocks.ArrayHelpers as SBBA
import qualified Stan.BuildingBlocks.Distributions as SBD

import Effectful (Eff)

vectorizeExpr :: SL.IntE -> SL.VarName -> (SL.IntE -> SL.RealE) -> SL.CodeWriter SL.VectorE
vectorizeExpr lE sn se = head <$> vectorizeExprT lE ((sn, se) :| [])

-- like vectorizeExpr but for multiple things in same loop
vectorizeExprT :: Traversable t
               => SL.IntE -> t (SL.VarName, SL.IntE -> SL.RealE) -> SL.CodeWriter (t (SL.UExpr SL.ECVec))
vectorizeExprT lengthE namedSrcs = do
  let vecVname sn = sn <> "_v"
      nds sn = SL.NamedDeclSpec (vecVname sn) $ SL.vectorSpec lengthE
      declareVec (sn, ve) = do
        fe <- SL.declareNW $ nds sn
        return (fe, ve)
      fillVec ne (ve, se) = SL.sliceE SL.s0 ne ve `SL.assign` se ne
  varExps <- traverse declareVec namedSrcs
  SL.addStmt $ SL.for "n" (SL.SpecificNumbered (SL.intE 1) lengthE) $ \nE -> SL.grouped $ fmap (fillVec nE) varExps
  return $ fst <$> varExps

diagVectorFunction :: SB.StanFunctionsC es => Eff es (SL.Function SL.ECVec '[SL.EArray1 SL.ECVec, SL.EInt])
diagVectorFunction = do
  let f :: SL.Function SL.ECVec '[SL.EArray1 SL.ECVec, SL.EInt]
      f = SL.simpleFunction "index_both"
      dsF :: SL.ExprList [SL.EArray1 SL.ECVec, SL.EInt] -> SL.DeclSpec SL.UExpr SL.ECVec
      dsF (_ :> n :> TNil) = SL.vectorSpec n
  _ <- SB.addFunctionOnce f (SL.Arg "vs" :> SL.Arg "N" :> TNil)
    $ SL.simpleFunctionBody f "out_vec" dsF
    $ \rvE (vs :> n :> TNil) ->
        [SL.for "n" (SL.SpecificNumbered (SL.intE 1) n) $ \nE ->
            let slice = SL.slice0 nE in slice rvE SL.|=| slice (SL.slice0 nE vs)]

  return f

weightedMeanFunction :: SB.StanFunctionsC es => Eff es (SL.Function SL.EReal [SL.ECVec, SL.ECVec])
weightedMeanFunction = do
  let f :: SL.Function SL.EReal [SL.ECVec, SL.ECVec]
      f = SL.simpleFunction "weighted_mean"
  SB.addFunctionOnce f (SL.Arg "ws" :> SL.Arg "xs" :> TNil)
    $ \(ws :> xs :> TNil)  -> SL.cwStmt $ do
    wgtdXs <- SL.declareRHSNW (SL.NamedDeclSpec "wgtdXs" $ SL.vectorSpec (SF.size xs)) $ ws |.*| xs
    return $ SF.sum wgtdXs |/| SF.sum ws

weightedMeanVarianceFunction :: SB.StanFunctionsC es => Eff es (SL.Function (SL.ETuple [SL.EReal, SL.EReal]) [SL.ECVec, SL.ECVec])
weightedMeanVarianceFunction = do
  let f :: SL.Function (SL.ETuple [SL.EReal, SL.EReal]) [SL.ECVec, SL.ECVec]
      f = SL.simpleFunction "weighted_mean_variance"
--      eTimes = SL.binaryOpE (SL.SElementWise SL.SMultiply)
  SB.addFunctionOnce f (SL.Arg "ws" :> SL.Arg "xs" :> TNil)
    $ \(ws :> xs :> TNil) -> SL.cwStmt $ do
    n <- SL.declareRHSW "N" SL.intSpec $ SF.size xs
    wgtdXs <- SL.declareRHSW "wgtdXs" (SL.vectorSpec n) $ ws |.*| xs
    mv <- SL.declareW "meanVar" (SL.tuple2Spec SL.realSpec SL.realSpec)
    let mvFst = SL.indexTuple SL.s0 mv
--    let meanVar i = SL.slice0 (SL.intE i) mv
    SL.addStmt $  mvFst SL.|=| (SF.sum wgtdXs |/| SF.sum ws)
    y <- SL.declareRHSW "y" (SL.vectorSpec n) $ xs |-| mvFst
    SL.addStmt $ SL.indexTuple SL.s1 mv SL.|=| (SF.sum (ws |.*| y |.*| y) |/| SF.sum ws)
    return mv

unWeightedMeanVarianceFunction :: SB.StanFunctionsC es => Eff es (SL.Function (SL.ETuple [SL.EReal, SL.EReal]) '[SL.ECVec])
unWeightedMeanVarianceFunction =
  SB.addFunctionOnce (SL.simpleFunction "unweighted_mean_variance") (SL.Arg "xs" :> TNil)
  $ \(xs :> TNil) -> SL.cwStmt $ pure $ SL.tupleE (SF.mean xs :> SF.variance xs :> TNil)


realIntRatio :: SL.UExpr SL.EInt -> SL.UExpr SL.EInt -> SL.UExpr SL.EReal
realIntRatio k l = let f x = (SL.realE 1 `SL.timesE` x) in f k `SL.divideE` f l

declTranspose :: SB.StanCodeC es
              => SL.NamedDeclSpec (SL.UnaryResultT SL.UTranspose t)
              -> SL.UExpr t
              -> Eff es (SL.UExpr (SL.UnaryResultT SL.UTranspose t))
declTranspose nds m = do
  SB.addFromCodeWriter $ SL.declareRHSNW nds $ SL.unaryOpE SL.STranspose m

indexedConstIntArray :: SB.StanCodeC es => SB.RowTypeTag i r -> Maybe Text -> SL.UExpr SL.EInt -> SL.UExpr SL.EInt -> Eff es SL.IntArrayE
indexedConstIntArray rtt mSuffix lengthE nE =
  let dsName = SB.dataSetName rtt
--      sizeName = SB.dataSetSizeName rtt
      nds = SL.NamedDeclSpec ("constIndex_" <> dsName <> maybe "" ("_" <>) mSuffix) $ SL.intArraySpec lengthE
  in SB.inBlock SL.SBTransformedData
     $ SB.addFromCodeWriter $ SL.declareRHSNW nds $ SF.rep_array1 nE lengthE

zeroVectorE :: SL.IntE -> SL.VectorE
zeroVectorE lengthE = SF.rep_vector (SL.realE 0) lengthE

zeroMatrixE :: SL.IntE -> SL.IntE -> SL.MatrixE
zeroMatrixE rowsE colsE = SF.rep_matrix (SL.realE 0) rowsE colsE

reIndex :: SL.IntArrayE -> (SL.IntE -> SL.UExpr t) -> SL.IntE -> SL.UExpr t
reIndex ia eF ke = eF $ SL.slice0 ke ia


{-
stackDataSets :: forall md gq r1 r2. (Typeable r1, Typeable r2)
                       => Text
                       -> SB.RowTypeTag r1
                       -> SB.RowTypeTag r2
                       -> SB.GroupSet -- groups to stack
                       -> SB.StanBuilderM md gq (SB.RowTypeTag (Either r1 r2) -- tag for combined loops
                                                , SB.StanName -> SME.StanVar -> SME.StanVar -> SB.StanBuilderM md gq SME.StanVar -- stack variables
                                             )
stackDataSets name rtt1 rtt2 groups = do
  let n1 = SB.dataSetName rtt1
      n2 = SB.dataSetName rtt2
      sizeName x = "N_" <> x
  listF1 <- SB.getModelDataFoldableAsListF rtt1
  listF2 <- SB.getModelDataFoldableAsListF rtt2
  rtt <- SB.addModelDataSet name (SB.ToFoldable $ \md -> (Left <$> listF1 md) ++ (Right <$> listF2 md))
  SB.addUseBindingToDataSet rtt n1 $ SB.StanVar ("N_" <> n1) SB.StanInt
  SB.addUseBindingToDataSet rtt n2 $ SB.StanVar ("N_" <> n2) SB.StanInt
  SB.inBlock SB.SBTransformedData $ do
    sizeV <- SB.stanDeclareRHS (sizeName name) SME.StanInt "<lower=0>"
             $ SME.name (sizeName n1) `SME.plus` SME.name (sizeName n2)
    SB.addDeclBinding name sizeV
    SB.addUseBindingToDataSet rtt name sizeV
  let copyUseBinding rttFrom rttTo dimName = do
        m <- SB.getDataSetBindings rttFrom
        case Map.lookup dimName m of
          Just e -> SB.addUseBindingToDataSet' rttTo dimName e
          Nothing -> SB.stanBuildError
                     $ "stackDataSets.copyUseBinding: " <> dimName <> " not found in data-set="
                     <> SB.dataSetName rtt <> " (inputeType=" <> show (SB.inputDataType rtt) <>")."
      copyIfNamed rttFrom rttTo d = case d of
        SB.NamedDim ik -> copyUseBinding rttFrom rttTo ik
        _ -> pure ()
      stackVars vName v1@(SB.StanVar _ t1) v2@(SB.StanVar _ t2) = do
        let stackTypesErr :: SB.StanBuilderM md gq a
            stackTypesErr = SB.stanBuildError $ "BuildingBlocks.stackDataSets.stackVars: Bad variables for stacking: v1=" <> show v1 <> "; v2=" <> show v2
        case (t1, t2) of
          (SB.StanVector (SB.NamedDim n1), SB.StanVector (SB.NamedDim n2)) ->
            SB.stanDeclareRHS vName (SB.StanVector $ SB.NamedDim name) "" $ SB.function "append_row" (SB.varNameE v1 :| [SB.varNameE v2])
          (SB.StanMatrix (SB.NamedDim n1, cd1), SB.StanMatrix (SB.NamedDim n2, cd2)) -> do
            when (cd1 /= cd2) stackTypesErr
            copyIfNamed rtt1 rtt cd1
            SB.useDataSetForBindings rtt
              $ SB.stanDeclareRHS vName (SB.StanMatrix (SB.NamedDim name, cd1)) "" $ SB.function "append_row" (SB.varNameE v1 :| [SB.varNameE v2])
          (SB.StanArray (SB.NamedDim n1 : ads1) at1, SB.StanArray (SB.NamedDim n2 : ads2) at2) -> do
            when ((ads1 /= ads2) || (at1 /= at2)) stackTypesErr
            mapM_ (copyIfNamed rtt1 rtt) (ads1 ++ SB.getDims at1)
            SB.useDataSetForBindings rtt
              $ SB.stanDeclareRHS vName (SB.StanArray (SB.NamedDim name : ads1) at1) "" $ SB.function "append_array" (SB.varNameE v1 :| [SB.varNameE v2])
          _ -> stackTypesErr
      stackGroupIndexes :: forall k. SB.GroupTypeTag k -> SB.Phantom k -> SB.StanBuilderM md gq (SB.Phantom k)
      stackGroupIndexes gtt _ = do
        let gName = SB.taggedGroupName gtt
        iv1 <- SB.getGroupIndexVar rtt1 gtt
        iv2 <- SB.getGroupIndexVar rtt2 gtt
        iv <- SB.inBlock SB.SBTransformedData $ do
          SB.setDataSetForBindings rtt
          stackVars (name <> "_" <> gName) iv1 iv2
        SB.addUseBindingToDataSet rtt gName iv
        return SB.Phantom
  _ <- DHash.traverseWithKey stackGroupIndexes groups
  return (rtt, stackVars)
-}

{-
groupDataSetMembershipMatrix :: SB.IndexKey -> SB.RowTypeTag r -> SB.StanBuilderM env d SB.StanVar
groupDataSetMembershipMatrix groupIndexKey rttD = SB.inBlock SB.SBTransformedData $ SB.useDataSetForBindings rttD $ do
  let dsIndexKey = SB.dataSetName rttD
      mType = SB.StanMatrix (SB.NamedDim groupKey, SB.NamedDim dsIndexKey)
      mName = groupIndexKey <> "_" <> dsIndexKey <> "_MM"
  sv <- SB.stanDeclare mName mType "<lower=0, upper=1>"
  SB.stanForLoopB "n" Nothing dsIndexKey
    $ SB.stanForLoopB "g"
-}



{-
addMultiIndex :: SB.RowTypeTag r -> [DHash.Some GroupTypeTag] -> Maybe Text -> SB.StanBuilderM env d SB.StanVar
addMultiIndex rtt gtts mVarName = do
  -- check that all indices are present
  rowInfo <- SB.rowInfo rtt
  let checkGroup :: Some GroupTypeTag -> SB.StanBuilderM env d ()
      checkGroup sg = case sg of
        DHash.Some gtt -> case DHash.lookup gtt (SB.groupIndexes rowInfo) of
          Nothing -> SB.stanBuildError $ "addMultiIndex: group " <> Sb.taggedGroupName gtt <> " is missing from group indexes for data-set " <> SB.dataSetName rtt <> "."
          Just _ -> return ()
  mapM_ checkGroup gtts
-}
