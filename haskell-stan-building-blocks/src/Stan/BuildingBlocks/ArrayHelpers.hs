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

module Stan.BuildingBlocks.ArrayHelpers
  (
    applyToArrayOf
  , applyToArrayOf'
  , ArrayList
  , ArrayWrapper(..)
  )
where

import qualified Stan.Language as SL
import Stan.Language.Recursion (hfmap)
import Stan.Language (TypedList(..))

import qualified Data.Vec.Lazy as Vec
import qualified Data.Type.Nat as DT
import Data.Type.Equality (type (:~:)(..))

-- wrapper for arrays of dimesnion n where the final type parameter is the type in the array
newtype ArrayWrapper n t = ArrayWrapper { getArray :: SL.UExpr (SL.EArray (DT.S n) t)}

-- type synonym for typed lists of arrays of different underlying types
type ArrayList n qs = SL.TypedList (ArrayWrapper n) qs

-- given a typed-list of same-dimension n arrays and a vector of length n+1 of indexes,
-- produce a typed-list of the elements of the arrays at that index.
-- There are no guarantees that the arrays all have elements at those indices
sliceArrayListAll :: Vec.Vec (DT.S n) SL.IntE -> ArrayList n qs -> SL.ExprList qs
sliceArrayListAll vecIndexes = hfmap (\x -> SL.sliceArrayAll (getArray x) vecIndexes)

-- apply a function taking a list of arguments to a list of arrays with the
-- matching types producing an array of results.
applyToArrayOf' :: forall n qs t.
                  (SL.SameTypedListToVecF SL.UExpr SL.EInt n
                  , SL.VecToSameTypedListF SL.VarAndForType SL.EInt n
                  , DT.SNatI n
                  )
               => Text
               -> (SL.ExprList qs -> SL.UExpr t)
               -> Vec.Vec (DT.S n) SL.IntE
               -> ArrayList n qs
               -> SL.UExpr (SL.EArray (DT.S n) t)
               -> SL.CodeWriter ()
applyToArrayOf' counterPrefix eltF arrDims es1 e2 = do
  SL.addStmt
    $ SL.intVecLoops @_ counterPrefix arrDims
    $ \dimEs
      -> case SL.getFESAProof (SL.fesaProofI @SL.EInt (DT.snat @n)) of
           Refl -> let vecIndexes = SL.sameTypedListToVec dimEs
                   in SL.sliceArrayAll @n e2 vecIndexes SL.|=| eltF (sliceArrayListAll @n vecIndexes es1)


-- apply a function taking one argument to an array of that type, producing an array of results
applyToArrayOf  :: forall n t' t.
                  (SL.SameTypedListToVecF SL.UExpr SL.EInt n
                  , SL.VecToSameTypedListF SL.VarAndForType SL.EInt n
                  , DT.SNatI n
                  )
               => Text
               -> (SL.UExpr t' -> SL.UExpr t)
               -> Vec.Vec (DT.S n) SL.IntE
               -> SL.UExpr (SL.EArray (DT.S n) t')
               -> SL.UExpr (SL.EArray (DT.S n) t)
               -> SL.CodeWriter ()
applyToArrayOf cp eltF arrDims e1 = applyToArrayOf' cp (\(x :> TNil) -> eltF x) arrDims (ArrayWrapper e1 :> TNil)


{-
data PlainOrArrayOf t where
  Plain :: TE.UExpr t -> PlainOrArrayOf t
  ArrOf :: ArrayOf n t -> PlainOrArrayOf t

applyToPlainOrArrayOf' :: Text -> (TE.ExprList qs -> TE.UExpr t)
-}
