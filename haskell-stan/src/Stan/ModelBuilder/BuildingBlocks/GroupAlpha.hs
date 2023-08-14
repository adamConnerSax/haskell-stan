{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE QuantifiedConstraints #-}

module Stan.ModelBuilder.BuildingBlocks.GroupAlpha
  (
    module Stan.ModelBuilder.BuildingBlocks.GroupAlpha
  )
where


import qualified Stan.ModelBuilder.TypedExpressions.Types as TE
import Stan.ModelBuilder.TypedExpressions.TypedList (TypedList(..))
import qualified Stan.ModelBuilder.TypedExpressions.Statements as TE
import qualified Stan.ModelBuilder.TypedExpressions.Indexing as TE
import qualified Stan.ModelBuilder.TypedExpressions.Operations as TE
import qualified Stan.ModelBuilder.TypedExpressions.Functions as TE
import qualified Stan.ModelBuilder.TypedExpressions.StanFunctions as SF
import qualified Stan.ModelBuilder.TypedExpressions.DAG as DAG
import qualified Stan.ModelBuilder.TypedExpressions.DAGTypes as DAG
import qualified Stan.ModelBuilder as SB
import qualified Stan.ModelBuilder.Distributions as SMD

import Prelude hiding (sum, All)
import qualified Data.Dependent.Sum as DSum
import qualified Data.Dependent.HashMap as DHash
import qualified Data.Vector.Unboxed as VU
import qualified Stan.ModelConfig as SB
import Stan.ModelBuilder.BuilderTypes (dataSetSizeName)

addModelIndexes :: forall a b md gq .

                   SB.RowTypeTag a
                -> (a -> b)
                -> [DSum.DSum SB.GroupTypeTag (GroupFromData b)]
                -> SB.StanGroupBuilderM md gq ()
addModelIndexes rtt f gfds = traverse_ g gfds where
  g :: DSum.DSum SB.GroupTypeTag (GroupFromData b) -> SB.StanGroupBuilderM md gq ()
  g (gtt DSum.:=> gfd) = do
    let (GroupFromData _ mi _) = contraGroupFromData f gfd
    SB.addGroupIndexForData gtt rtt mi

addGroupIntMaps :: forall a b md gq .
                   SB.RowTypeTag a
                -> (a -> b)
                -> [DSum.DSum SB.GroupTypeTag (GroupFromData b)]
                -> SB.StanGroupBuilderM md gq ()
addGroupIntMaps rtt f gfds = traverse_ g gfds where
  g :: DSum.DSum SB.GroupTypeTag (GroupFromData b) -> SB.StanGroupBuilderM md gq ()
  g (gtt DSum.:=> gfd) = do
    let (GroupFromData _ _ gim) = contraGroupFromData f gfd
    SB.addGroupIntMapForDataSet gtt rtt gim

data AlphaByDataVecCW md gq where
  AlphaByDataVecCW :: (forall a . SB.RowTypeTag a -> SB.StanBuilderM md gq (TE.CodeWriter TE.VectorE)) -> AlphaByDataVecCW md gq

-- Do one time per model things: add parameters, etc.
setupAlpha :: forall md gq . GroupAlpha -> SB.StanBuilderM md gq (AlphaByDataVecCW md gq)
setupAlpha (GroupAlphaE bp avE) = do
  aE <- DAG.parameterExpr <$> DAG.addBuildParameter bp
  let  f :: SB.RowTypeTag a -> SB.StanBuilderM md gq (TE.CodeWriter TE.VectorE)
       f rtt = pure $ pure $ avE aE rtt
  pure $ AlphaByDataVecCW f
setupAlpha (GroupAlphaCW bp avCW) = do
  aE <- DAG.parameterExpr <$> DAG.addBuildParameter bp
  let f :: SB.RowTypeTag a -> SB.StanBuilderM md gq (TE.CodeWriter TE.VectorE)
      f rtt = pure $ avCW aE rtt
  pure $ AlphaByDataVecCW f
setupAlpha (GroupAlphaTD bp tdCW avCW) = do
  aE <- DAG.parameterExpr <$> DAG.addBuildParameter bp
  let f :: SB.RowTypeTag a -> SB.StanBuilderM md gq (TE.CodeWriter TE.VectorE)
      f rtt = do
        let block = case SB.inputDataType rtt of
              SB.ModelData -> SB.SBTransformedData
              SB.GQData -> SB.SBTransformedDataGQ
        td <- SB.inBlock block $ SB.addFromCodeWriter $ tdCW rtt
        pure $ avCW td aE rtt
  pure $ AlphaByDataVecCW f
setupAlpha (GroupAlphaPrep bp prep avCW) = do
  aE <- DAG.parameterExpr <$> DAG.addBuildParameter bp
  let f :: SB.RowTypeTag a -> SB.StanBuilderM md gq (TE.CodeWriter TE.VectorE)
      f rtt = do
        let block = case SB.inputDataType rtt of
              SB.ModelData -> SB.SBTransformedData
              SB.GQData -> SB.SBTransformedDataGQ
        a <- prep rtt
        pure $ avCW a aE rtt
  pure $ AlphaByDataVecCW f

-- do once per data-set things and sum
setupAlphaSum :: forall md gq . NonEmpty GroupAlpha -> SB.StanBuilderM md gq (AlphaByDataVecCW md gq)
setupAlphaSum gts = do
  abdvcws :: NonEmpty (AlphaByDataVecCW md gq) <- traverse setupAlpha gts
  let f :: SB.RowTypeTag a -> SB.StanBuilderM md gq (TE.CodeWriter TE.VectorE)
      f rtt = do
        x <- traverse (\abdv -> let (AlphaByDataVecCW g) = abdv in g rtt) abdvcws
        pure $ fmap (\z -> foldl' TE.plusE (head z) (tail z)) $ sequence x
  pure $ AlphaByDataVecCW f

{-
setupAlphaSum :: forall md gq . NonEmpty GroupAlpha -> AlphaByDataVecCW md gq
setupAlphaSum gts =
  let abdvcws :: NonEmpty (AlphaByDataVecCW md gq) = fmap setupAlpha gts
      f :: SB.RowTypeTag a -> SB.StanBuilderM md gq (TE.CodeWriter TE.VectorE)
      f rtt = do
        x <- traverse (\abdv -> let (AlphaByDataVecCW g) = abdv in g rtt) abdvcws
        pure $ fmap (\z -> foldl' TE.plusE (head z) (tail z)) $ sequence x
  in AlphaByDataVecCW f
-}



data GroupFromData r k = GroupFromData { gfdGroup :: r -> k
                                       , gfdMakeIndex :: SB.MakeIndex r k
                                       , gfdMakeIntMap :: SB.DataToIntMap r k
                                       }

groupFromDataEnum :: (Show k, Enum k, Bounded k, Ord k) => (r -> k) -> GroupFromData r k
groupFromDataEnum f = GroupFromData f (SB.makeIndexFromEnum f) (SB.dataToIntMapFromEnum f)

contraGroupFromData :: (a -> b) -> GroupFromData b k -> GroupFromData a k
contraGroupFromData f (GroupFromData g mi di) = GroupFromData (g . f) (SB.contraMakeIndex f mi) (SB.contraDataToIntMap f di)

data GroupAlpha where
  GroupAlphaE :: forall t . DAG.BuildParameter t
             -> (forall a . TE.UExpr t -> SB.RowTypeTag a -> TE.VectorE)
             -> GroupAlpha
  GroupAlphaCW :: forall t . DAG.BuildParameter t
               -> (forall a . TE.UExpr t -> SB.RowTypeTag a -> TE.CodeWriter TE.VectorE)
               -> GroupAlpha
  GroupAlphaTD :: forall t td . DAG.BuildParameter t
               -> (forall a . SB.RowTypeTag a -> TE.CodeWriter td)
               -> (forall a . td -> TE.UExpr t -> SB.RowTypeTag a -> TE.CodeWriter TE.VectorE)
               -> GroupAlpha
  GroupAlphaPrep :: forall t p . DAG.BuildParameter t
                 -> (forall a md gq . SB.RowTypeTag a -> SB.StanBuilderM md gq p)
                 -> (forall a . p -> TE.UExpr t -> SB.RowTypeTag a -> TE.CodeWriter TE.VectorE)
                 -> GroupAlpha



--zeroOrderAlpha :: DAG.BuildParameter TE.EReal -> GroupAlpha r TE.EReal
--zeroOrderAlpha n bp = GroupAlpha bp (\_ -> pure (\t -> t))

binaryAlpha :: Eq k => SB.GroupTypeTag k -> DAG.BuildParameter TE.EReal -> GroupAlpha
binaryAlpha gtt bp = GroupAlphaTD bp tdCW f where
  indexVec :: SB.RowTypeTag a -> TE.VectorE
  indexVec rtt = TE.functionE SF.to_vector (SB.byGroupIndexE rtt gtt :> TNil)
  splitIndexNDS :: SB.RowTypeTag a -> TE.NamedDeclSpec TE.ECVec
  splitIndexNDS rtt = TE.NamedDeclSpec ("splitIndex_" <> SB.taggedGroupName gtt <> "_" <> SB.dataSetName rtt) $ TE.vectorSpec (SB.dataSetSizeE rtt) []
  tdCW :: SB.RowTypeTag a -> TE.CodeWriter TE.VectorE
  tdCW rtt = TE.declareRHSNW (splitIndexNDS rtt) $ TE.realE 1.5 `TE.minusE` indexVec rtt

  f :: TE.VectorE -> TE.UExpr TE.EReal -> SB.RowTypeTag a -> TE.CodeWriter TE.VectorE
  f splitIndex aE rtt = pure $ aE `TE.timesE` splitIndex

firstOrderAlpha :: SB.GroupTypeTag k -> DAG.BuildParameter TE.ECVec -> GroupAlpha
firstOrderAlpha gtt bp = GroupAlphaE bp f where
  f :: forall a md gq . TE.VectorE -> SB.RowTypeTag a -> TE.VectorE
  f aE rtt = TE.indexE TE.s0 (SB.byGroupIndexE rtt gtt) aE


-- dummy coding. For now just append 0. Would be helpful to choose where to put the zero so we could
-- choose which entry to dummy code.
firstOrderAlphaDC :: SB.GroupTypeTag k -> k -> DAG.BuildParameter TE.ECVec -> GroupAlpha
firstOrderAlphaDC gtt controlK bp = GroupAlphaPrep bp prep f where
  prep :: SB.RowTypeTag a -> SB.StanBuilderM md gq (TE.Function TE.ECVec [TE.ECVec, TE.EInt], Int)
  prep rtt = do
    insert_zero_at <- insertZeroAtFunction
    (SB.IndexMap _ kgi _ _) <- SB.indexMap rtt gtt
    cn <- SB.stanBuildEither $ kgi controlK
    pure (insert_zero_at, cn)
  f :: forall a md gq . (TE.Function TE.ECVec [TE.ECVec, TE.EInt], Int) -> TE.VectorE -> SB.RowTypeTag a -> TE.CodeWriter TE.VectorE
  f (insert_zero_at, cn) aE rtt = do
    let aDCNDS = TE.NamedDeclSpec (DAG.bParameterName bp <> "_dc") $ TE.vectorSpec (SB.groupSizeE gtt) []
--    aDC <- TE.declareRHSNW aDCNDS $ TE.functionE SF.append_to_vector (aE :> TE.realE 0 :> TNil)
    aDC <- TE.declareRHSNW aDCNDS $ TE.functionE insert_zero_at (aE :> TE.intE cn :> TNil)
    pure $ TE.indexE TE.s0 (SB.byGroupIndexE rtt gtt) aDC

secondOrderAlpha :: SB.GroupTypeTag k
                 -> SB.GroupTypeTag k
                 -> DAG.BuildParameter TE.EMat
                 -> GroupAlpha
secondOrderAlpha gtt1 gtt2 bp = GroupAlphaCW bp f where
  f :: forall a md gq . TE.MatrixE -> SB.RowTypeTag a -> TE.CodeWriter TE.VectorE
  f aM rtt = do
    let index1 = SB.byGroupIndexE rtt gtt1
        index2 = SB.byGroupIndexE rtt gtt2
        alphaVNDS = TE.NamedDeclSpec ("aVec_" <> SB.taggedGroupName gtt1 <> "_" <> SB.taggedGroupName gtt2)
                 $ TE.vectorSpec (SB.dataSetSizeE rtt) []
        reIndexedAlpha = TE.indexE TE.s1 (SB.byGroupIndexE rtt gtt2)$ TE.indexE TE.s0 (SB.byGroupIndexE rtt gtt1) aM

    aV <- TE.declareNW alphaVNDS
    TE.addStmt
      $ TE.for "n" (TE.SpecificNumbered (TE.intE 1) $ SB.dataSetSizeE rtt)
      $ \nE -> [(aV `TE.at` nE) `TE.assign` TE.mAt reIndexedAlpha nE nE]
    pure aV


insertZeroAtFunction :: SB.StanBuilderM md gq (TE.Function TE.ECVec [TE.ECVec, TE.EInt])
insertZeroAtFunction = do
  let le = TE.boolOpE TE.SLT
      eq = TE.boolOpE TE.SEq
      f :: TE.Function TE.ECVec [TE.ECVec, TE.EInt]
      f = TE.simpleFunction "insert_zero_at"
  SB.addFunctionOnce f (TE.Arg "v" :> TE.Arg "n" :> TNil)
    $ \(v :> n :> TNil)  -> TE.writerL $ do
    szE <- TE.declareRHSNW (TE.NamedDeclSpec "m" $ TE.intSpec []) $ TE.functionE SF.size (v :> TNil) `TE.plusE` TE.intE 1
    wzero <- TE.declareNW (TE.NamedDeclSpec "wz" $ TE.vectorSpec szE [])
--             $ TE.functionE SF.rep_vector (TE.realE 0 :> szE :> TNil)
    TE.addStmt $ TE.for "l" (TE.SpecificNumbered (TE.intE 1) szE)
      $ \l -> [TE.ifThenElse
                ((l `le` n, (wzero `TE.at` l) `TE.assign` (v `TE.at` l)) :|
                [(l `eq` n, (wzero `TE.at` l) `TE.assign` TE.realE 0)])
                ((wzero `TE.at` l) `TE.assign` (v `TE.at` (l `TE.minusE` TE.intE 1)))]
    return wzero
