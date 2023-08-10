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
import qualified Stan.ModelBuilder.TypedExpressions.StanFunctions as SF
import qualified Stan.ModelBuilder.TypedExpressions.DAG as DAG
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

type AlphaByDataVecCW md gq = forall a . SB.RowTypeTag a -> SB.StanBuilderM md gq (TE.CodeWriter TE.VectorE)

setupAlpha :: forall md gq . GroupAlpha -> AlphaByDataVecCW md gq
setupAlpha (GroupAlphaE bp avE) rtt = do
  aE <- DAG.parameterExpr <$> DAG.addBuildParameter bp
  pure $ pure $ avE aE rtt
setupAlpha (GroupAlphaCW bp avCW) rtt = do
  aE <- DAG.parameterExpr <$> DAG.addBuildParameter bp
  pure $ avCW aE rtt
setupAlpha (GroupAlphaTD bp tdCW avCW) rtt = do
  aE <- DAG.parameterExpr <$> DAG.addBuildParameter bp
  td <- SB.inBlock SB.SBTransformedData $ SB.addFromCodeWriter $ tdCW rtt
  pure $ avCW td aE rtt

setupAlphaSum :: forall md gq . NonEmpty GroupAlpha -> AlphaByDataVecCW md gq
setupAlphaSum gts rtt = do
  cws :: NonEmpty (TE.CodeWriter TE.VectorE) <- traverse (flip setupAlpha rtt) gts
  pure $ (\x -> foldl' TE.plusE (head x) (tail x)) <$> sequence cws

{-  let f :: SB.RowTypeTag a -> SB.StanBuilderM md gq (TE.CodeWriter TE.VectorE)
      f rtt = do
        cws :: NonEmpty (TE.CodeWriter TE.VectorE) <- traverse (\af -> af rtt) afs
        let cwvs :: TE.CodeWriter (NonEmpty TE.VectorE) = sequence cws
        pure $ fmap (\vs -> foldl' TE.plusE (head vs) (tail vs)) cwvs
  pure f
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


--zeroOrderAlpha :: DAG.BuildParameter TE.EReal -> GroupAlpha r TE.EReal
--zeroOrderAlpha n bp = GroupAlpha bp (\_ -> pure (\t -> t))

binaryAlpha :: Eq k => SB.GroupTypeTag k -> DAG.BuildParameter TE.EReal -> GroupAlpha
binaryAlpha gtt bp = GroupAlphaTD bp tdCW f where
  indexVec :: SB.RowTypeTag a -> TE.VectorE
  indexVec rtt = TE.functionE SF.to_vector (SB.byGroupIndexE rtt gtt :> TNil)
  splitIndexNDS :: SB.RowTypeTag a -> TE.NamedDeclSpec TE.ECVec
  splitIndexNDS rtt = TE.NamedDeclSpec ("splitIndex_" <> SB.taggedGroupName gtt) $ TE.vectorSpec (SB.dataSetSizeE rtt) []
  tdCW :: SB.RowTypeTag a -> TE.CodeWriter TE.VectorE
  tdCW rtt = TE.declareRHSNW (splitIndexNDS rtt) $ TE.realE 1.5 `TE.minusE` indexVec rtt

  f :: TE.VectorE -> TE.UExpr TE.EReal -> SB.RowTypeTag a -> TE.CodeWriter TE.VectorE
  f splitIndex aE rtt = pure $ aE `TE.timesE` splitIndex


firstOrderAlpha :: SB.GroupTypeTag k -> DAG.BuildParameter TE.ECVec -> GroupAlpha
firstOrderAlpha gtt bp = GroupAlphaE bp f where
  f :: forall a md gq . TE.VectorE -> SB.RowTypeTag a -> TE.VectorE
  f aE rtt = TE.indexE TE.s0 (SB.byGroupIndexE rtt gtt) aE

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
