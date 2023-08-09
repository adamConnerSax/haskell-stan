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
import qualified Stan.ModelBuilder.TypedExpressions.DAGTypes as DAG
import qualified Stan.ModelBuilder as SB
import qualified Stan.ModelBuilder.Distributions as SMD

import Prelude hiding (sum, All)
import qualified Data.Dependent.Sum as DSum
import qualified Data.Dependent.HashMap as DHash
import qualified Data.Vector.Unboxed as VU
import qualified Stan.ModelConfig as SB
import Stan.ModelBuilder.BuilderTypes (dataSetSizeName)

data GroupFromData r k = GroupFromData { gfdGroup :: r -> k
                                       , gfdMakeIndex :: SB.MakeIndex r k
                                       , gfdMakeIntMap :: SB.DataToIntMap r k
                                       }

contraGroupFromData :: (a -> b) -> GroupFromData b k -> GroupFromData a k
contraGroupFromData f (GroupFromData g mi di) = GroupFromData (g . f) (SB.contraMakeIndex f mi) (SB.contraDataToIntMap f di)

data GroupAlpha r t = GroupAlpha { gaFromDataL :: [DSum.DSum SB.GroupTypeTag (GroupFromData r)]
                                 , gaPrior :: DAG.BuildParameter t
                                 , gaAlphaVecF :: forall a md gq . SB.RowTypeTag a -> TE.UExpr t -> SB.StanBuilderM md gq TE.VectorE
                                 }

contraGroupAlpha :: (a -> b) -> GroupAlpha b t -> GroupAlpha a t
contraGroupAlpha f (GroupAlpha fd bp rv) = GroupAlpha fd' bp rv where
  fd' = fmap (\(gtt DSum.:=> gfd) -> (gtt DSum.:=> contraGroupFromData f gfd)) fd

--zeroOrderAlpha :: TE.StanName -> DAG.BuildParameter TE.EReal -> GroupAlpha r TE.EReal
--zeroOrderAlpha n bp = GroupAlpha [] bp (\_ -> pure (\t -> t))

binaryAlpha :: (Eq k) => SB.GroupTypeTag k -> GroupFromData r k -> DAG.BuildParameter TE.EReal -> k -> GroupAlpha r TE.EReal
binaryAlpha gtt gfd bp posK = GroupAlpha [gtt DSum.:=> gfd] bp f where
  f :: forall a md gq . SB.RowTypeTag a -> TE.UExpr TE.EReal -> SB.StanBuilderM md gq TE.VectorE
  f rtt aE = do
    let indexVec = TE.functionE SF.to_vector (SB.byGroupIndexE rtt gtt :> TNil)
        splitIndexNDS = TE.NamedDeclSpec ("splitIndex_" <> SB.taggedGroupName gtt) $ TE.vectorSpec (SB.dataSetSizeE rtt) []
    splitIndex <- SB.inBlock SB.SBTransformedData
                  $ SB.addFromCodeWriter
                  $ TE.declareRHSNW splitIndexNDS
                  $ TE.realE 1.5 `TE.minusE` indexVec
    pure $ aE `TE.timesE` splitIndex


firstOrderAlpha :: SB.GroupTypeTag k -> GroupFromData r k -> DAG.BuildParameter TE.ECVec -> GroupAlpha r TE.ECVec
firstOrderAlpha gtt gfd bp = GroupAlpha [gtt DSum.:=> gfd] bp f where
  f :: forall a md gq . SB.RowTypeTag a -> TE.VectorE -> SB.StanBuilderM md gq TE.VectorE
  f rtt aE = pure $ TE.indexE TE.s0 (SB.byGroupIndexE rtt gtt) aE

secondOrderAlpha :: SB.GroupTypeTag k -> GroupFromData r k
                 -> SB.GroupTypeTag k -> GroupFromData r k
                 -> DAG.BuildParameter TE.EMat
                 -> GroupAlpha r TE.EMat
secondOrderAlpha gtt1 gfd1 gtt2 gfd2 bp = GroupAlpha [gtt1 DSum.:=> gfd1, gtt2 DSum.:=> gfd2] bp f where
  f :: forall a md gq . SB.RowTypeTag a -> TE.MatrixE -> SB.StanBuilderM md gq TE.VectorE
  f rtt aM = do
    let index1 = SB.byGroupIndexE rtt gtt1
        index2 = SB.byGroupIndexE rtt gtt2
        alphaVNDS = TE.NamedDeclSpec ("aVec_" <> SB.taggedGroupName gtt1 <> "_" <> SB.taggedGroupName gtt2)
                 $ TE.vectorSpec (SB.dataSetSizeE rtt) []
        reIndexedAlpha = TE.indexE TE.s1 (SB.byGroupIndexE rtt gtt2)$ TE.indexE TE.s0 (SB.byGroupIndexE rtt gtt1) aM
    SB.addFromCodeWriter $ do
      aV <- TE.declareNW alphaVNDS
      TE.addStmt
        $ TE.for "n" (TE.SpecificNumbered (TE.intE 1) $ SB.dataSetSizeE rtt)
        $ \nE -> [(aV `TE.at` nE) `TE.assign` TE.mAt reIndexedAlpha nE nE]
      pure aV
