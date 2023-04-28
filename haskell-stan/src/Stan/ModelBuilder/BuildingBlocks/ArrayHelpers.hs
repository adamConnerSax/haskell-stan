{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use for_" #-}
{-# HLINT ignore "Use camelCase" #-}

module Stan.ModelBuilder.BuildingBlocks.ArrayHelpers
  (
    module Stan.ModelBuilder.BuildingBlocks.ArrayHelpers
  )
where

import qualified Stan.ModelBuilder.TypedExpressions.Types as TE
import Stan.ModelBuilder.TypedExpressions.TypedList (TypedList(..))
import qualified Stan.ModelBuilder.TypedExpressions.TypedList as TL
import qualified Stan.ModelBuilder.TypedExpressions.Statements as TE
import Stan.ModelBuilder.TypedExpressions.Recursion (hfmap)

import qualified Data.Vec.Lazy as Vec
import qualified Data.Type.Nat as DT
import Data.Type.Equality (type (:~:)(..))

-- wrapper for arrays of length n where the final type parameter is the type in the array
newtype ArrayOf n t = ArrayOf { getArray :: TE.UExpr (TE.EArray (DT.S n) t)}

-- type synonym for typed lists of arrays of different underlying types
type ArrayList n qs = TL.TypedList (ArrayOf n) qs

-- given a typed-list of same-length arrays and a vector of that length of indexes,
-- produce a typed-list of the elements of the arrays at that index.
sliceArrayListAll :: Vec.Vec (DT.S n) TE.IntE -> ArrayList n qs -> TE.ExprList qs
sliceArrayListAll vecIndexes = hfmap (\x -> TE.sliceArrayAll (getArray x) vecIndexes)

-- apply a function taking a list of arguments to a list of arrays with the
-- matching types producing an array of results.
applyToArrayOf' :: forall n qs t.
                  (TL.SameTypedListToVecF TE.UExpr TE.EInt n
                  , TL.VecToSameTypedListF TE.VarAndForType TE.EInt n
                  , DT.SNatI n
                  )
               => Text
               -> (TE.ExprList qs -> TE.UExpr t)
               -> Vec.Vec (DT.S n) TE.IntE
               -> ArrayList n qs
               -> TE.UExpr (TE.EArray (DT.S n) t)
               -> TE.CodeWriter ()
applyToArrayOf' counterPrefix eltF arrDims es1 e2 = do
  TE.addStmt
    $ TE.intVecLoops @_ @[] counterPrefix arrDims
    $ \dimEs
      -> case TE.getFESAProof (TE.fesaProofI @TE.EInt (DT.snat @n)) of
           Refl -> let vecIndexes = TL.sameTypedListToVec dimEs
                   in [TE.sliceArrayAll @n e2 vecIndexes
                        `TE.assign` eltF (sliceArrayListAll @n vecIndexes es1)]


-- apply a function taking one argument to an array of that type, producing an array of results
applyToArrayOf  :: forall n t' t.
                  (TL.SameTypedListToVecF TE.UExpr TE.EInt n
                  , TL.VecToSameTypedListF TE.VarAndForType TE.EInt n
                  , DT.SNatI n
                  )
               => Text
               -> (TE.UExpr t' -> TE.UExpr t)
               -> Vec.Vec (DT.S n) TE.IntE
               -> TE.UExpr (TE.EArray (DT.S n) t')
               -> TE.UExpr (TE.EArray (DT.S n) t)
               -> TE.CodeWriter ()
applyToArrayOf cp eltF arrDims e1 = applyToArrayOf' cp (\(x :> TNil) -> eltF x) arrDims (ArrayOf e1 :> TNil)


{-
data PlainOrArrayOf t where
  Plain :: TE.UExpr t -> PlainOrArrayOf t
  ArrOf :: ArrayOf n t -> PlainOrArrayOf t

applyToPlainOrArrayOf' :: Text -> (TE.ExprList qs -> TE.UExpr t)
-}
