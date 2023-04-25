{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# LANGUAGE StandaloneKindSignatures #-}

module Stan.ModelBuilder.TypedExpressions.Types
  (
    module Stan.ModelBuilder.TypedExpressions.Types
  , Nat(..)
  , SNat(..)
  )
  where

import Prelude hiding (Nat)

import Data.Type.Equality ((:~:)(Refl), TestEquality(testEquality))
import Data.Type.Nat (Nat(..), SNat(..))
import qualified Data.Type.Nat as DT

import qualified GHC.TypeLits as TE
import GHC.TypeLits (ErrorMessage((:<>:)))
import qualified Text.Show

-- possible types of terms
-- NB: zero dimensional array will be treated as the underlying type
data EType where
  EVoid :: EType
  EString :: EType
  EBool :: EType
  EInt :: EType
  EReal :: EType
  EComplex :: EType
  ESimplex :: EType
  ECVec :: EType
  ERVec :: EType
  EMat :: EType
  ESqMat :: EType
  EArray :: Nat -> EType -> EType
--  (::->) :: EType -> EType -> EType
  deriving stock (Eq, Ord, Show)

type family ZeroDArray (e :: EType) :: EType where
  ZeroDArray (EArray (S n) _) =  TE.TypeError (TE.Text "ZeroDArray: " :<>: TE.ShowType n :<>: TE.Text " is not a zero dimensional array")
  ZeroDArray (EArray Z t) = t
  ZeroDArray t = t

class GenEType (e :: EType) where
  genEType :: EType

instance GenEType EVoid where genEType = EVoid
instance GenEType EString where genEType = EString
instance GenEType EBool where genEType = EBool
instance GenEType EInt where genEType = EInt
instance GenEType EReal where genEType = EReal
instance GenEType EComplex where genEType = EComplex
instance GenEType ESimplex where genEType = ESimplex
instance GenEType ECVec where genEType = ECVec
instance GenEType ERVec where genEType = ERVec
instance GenEType EMat where genEType = EMat
instance GenEType ESqMat where genEType = ESqMat
instance (DT.SNatI n, GenEType t) => GenEType (EArray n t) where genEType = EArray (DT.snatToNat $ DT.snat @n) (genEType @t)


type EArray1 :: EType -> EType
type EArray1 t = EArray (S Z) t

type EArray2 :: EType -> EType
type EArray2 t = EArray (S (S Z)) t

type EIndexArray :: EType
type EIndexArray = EArray1 EInt

type EIntArray :: EType
type EIntArray = EArray (S Z) EInt

type ERealArray :: EType
type ERealArray = EArray (S Z) EReal

type EComplexArray :: EType
type EComplexArray = EArray (S Z) EComplex


-- A mechanism to limit the types we can use in functions via a constraint
type TypeOneOf et ets = TypeOneOf' et ets (TypeOneOfB et ets)

type family TypeOneOfB (et :: EType) (ets :: [EType]) :: Bool where
  TypeOneOfB _ '[] = False
  TypeOneOfB et (et ': t) = True
  TypeOneOfB et (h ': t) = TypeOneOfB et t

type family TypeOneOf' (et :: EType) (ets :: [EType]) (mem :: Bool) :: Constraint where
  TypeOneOf' et ets 'True = ()
  TypeOneOf' et ets 'False = TE.TypeError (TE.ShowType et :<>: TE.Text " is not a member of " :<>: TE.ShowType ets)

{-
type family OrArrayOfB (et :: EType) (t :: EType) :: Bool where
  OrArrayOfB a a = True
  OrArrayOfB a (EArray1 a) = True
  OrArrayOfB EReal SCVec = True
  OrArrayOfB _ _ = False

type family ScalarOrArrayOf' (a :: EType) (b :: EType) (mem :: Bool) :: Constraint where
  ScalarOrArrayOf' a b 'True = '[]
  ScalarOrArrayOf a b 'False = TE.TypeError (TE.ShowType a :<>: TE.Text " is not a scalar or array of " :<>: TE.ShowType b)
-}

type family IfNumber (et :: EType) (a :: k) (b :: k) :: k where
  IfNumber EInt a _ = a
  IfNumber EReal a _ = a
  IfNumber EComplex a _ = a
  IfNumber _ _ b = b

type family IfRealNumber (et :: EType) (a :: k) (b :: k) :: k where
  IfRealNumber EInt a _ = a
  IfRealNumber EReal a _ = a
  IfRealNumber _ _ b = b


type family IfNumbers (a :: EType) (b :: EType) (c :: k) (d :: k) where
  IfNumbers a b c d = IfNumber a (IfNumber b c d) d

type family Promoted (a :: EType) (b :: EType) :: EType where
  Promoted a a = a
  Promoted EInt EReal = EReal
  Promoted EReal EInt = EReal
  Promoted EInt EComplex = EComplex
  Promoted EComplex EInt = EComplex
  Promoted EReal EComplex = EComplex
  Promoted EComplex EReal = EComplex
  Promoted a b = TE.TypeError (TE.Text "One of " :<>: TE.ShowType a :<>: TE.Text " and " :<>: TE.ShowType b :<>: TE.Text " isn't a promotable (number) type.")

--Stan's modifiers (e.g. "<lower=2>" apply to the internal type in an array.)
type family ScalarType (et :: EType) :: EType where
  ScalarType (EArray _ t) = ScalarType t
  ScalarType ESimplex = EReal
  ScalarType ECVec = EReal
  ScalarType ERVec = EReal
  ScalarType EMat = EReal
  ScalarType ESqMat = EReal
  ScalarType a = a

type family IsContainer (t :: EType) :: Constraint where
  IsContainer ESimplex = ()
  IsContainer ECVec = ()
  IsContainer ERVec = ()
  IsContainer EMat = ()
  IsContainer ESqMat = ()
  IsContainer (EArray _ _) = ()
  IsContainer t = TE.TypeError (TE.ShowType t :<>: TE.Text " is not a container type.  Perhaps you are trying to call segment or block?")

-- EType singleton
data SType :: EType -> Type where
  SVoid :: SType EVoid
  SString :: SType EString
  SBool :: SType EBool
  SInt :: SType EInt
  SReal :: SType EReal
  SComplex :: SType EComplex
  SSimplex :: SType ESimplex
  SCVec :: SType ECVec
  SRVec :: SType ERVec
  SMat :: SType EMat
  SSqMat :: SType ESqMat
  SArray :: SNat n -> SType t -> SType (EArray n t)
--  (:->) :: SType t -> SType t' -> SType (t ::-> t')

class GenSType (e :: EType) where
  genSType :: SType e

instance GenSType EVoid where genSType = SVoid
instance GenSType EString where genSType = SString
instance GenSType EBool where genSType = SBool
instance GenSType EInt where genSType = SInt
instance GenSType EReal where genSType = SReal
instance GenSType EComplex where genSType = SComplex
instance GenSType ESimplex where genSType = SSimplex
instance GenSType ECVec where genSType = SCVec
instance GenSType ERVec where genSType = SRVec
instance GenSType EMat where genSType = SMat
instance GenSType ESqMat where genSType = SSqMat
instance (DT.SNatI n, GenSType t) => GenSType (EArray n t) where genSType = SArray DT.snat (genSType @t)
--instance (GenSType ta, GenSType tb) => GenSType (ta ::-> tb) where genSType = genSType @ta :-> genSType @tb

type SArray1 t = SType (EArray (S Z) t)

type SIntArray = SArray1 EInt

sIntArray :: SIntArray
sIntArray = SArray SS SInt

sIndexArray :: SType EIndexArray
sIndexArray = sIntArray


instance Show (SType t) where
  show x = "SType: " <> show (sTypeToEType x)

instance Eq (SType t) where
  SVoid == SVoid = True
  SString == SString = True
  SBool == SBool = True
  SInt == SInt = True
  SReal == SReal = True
  SComplex == SComplex = True
  SSimplex == SSimplex = True
  SCVec == SCVec = True
  SRVec == SRVec = True
  SMat == SMat = True
  SSqMat == SSqMat = True
  SArray n st == SArray n' st' = (DT.snatToNat n == DT.snatToNat n') && (st == st')
--  sa :-> sb == sa' :-> sb' = (sa == sa') && (sb == sb')


sTypeToEType :: SType t -> EType
sTypeToEType = \case
  SVoid -> EVoid
  SString -> EString
  SBool -> EBool
  SInt -> EInt
  SReal -> EReal
  SComplex -> EComplex
  SSimplex -> ESimplex
  SCVec -> ECVec
  SRVec -> ERVec
  SMat -> EMat
  SSqMat -> ESqMat
  SArray sn st -> case DT.snatToNat sn of
    Z -> sTypeToEType st
    S n -> EArray (S n) $ sTypeToEType st
--  sa :-> sb -> sTypeToEType sa ::-> sTypeToEType sb

withSType :: forall r . EType -> (forall t. SType t -> r) -> r
withSType EVoid k = k SVoid
withSType EString k = k SString
withSType EBool k = k SBool
withSType EInt k = k SInt
withSType EReal k = k SReal
withSType EComplex k = k SComplex
withSType ESimplex k = k SSimplex
withSType ERVec k = k SRVec
withSType ECVec k = k SCVec
withSType EMat k = k SMat
withSType ESqMat k = k SSqMat
withSType (EArray n t) k = DT.reify n f
  where
    f :: forall n. DT.SNatI n => Proxy n -> r
    f _ = withSType t $ \st -> k (SArray (DT.snat @n)  st)
--withSType (a ::-> b) k = withSType a $ \sa -> withSType b $ \sb -> k (sa :-> sb)

sTypeName :: SType t -> Text
sTypeName = \case
  SVoid -> "void"
  SString -> "string"
  SBool -> "bool"
  SInt -> "int"
  SReal -> "real"
  SComplex -> "complex"
  SSimplex -> "simplex"
  SCVec -> "vector"
  SRVec -> "row_vector"
  SMat -> "matrix"
  SSqMat -> "matrix"
  SArray _ _ -> "array"
--  (:->) _ _ -> "funcApply"

data StanType :: EType -> Type where
--  StanVoid :: StanType EVoid
--  StanString :: StanType EString
--  StanBool :: StanType EBool
  StanInt :: StanType EInt
  StanReal :: StanType EReal
  StanComplex :: StanType EComplex
  StanArray :: SNat n -> StanType et -> StanType (EArray n et)
  StanVector :: StanType ECVec
  StanOrdered :: StanType ECVec
  StanPositiveOrdered :: StanType ECVec
  StanSimplex :: StanType ESimplex
  StanUnitVector :: StanType ECVec
  StanRowVector :: StanType ERVec
  StanMatrix :: StanType EMat
  StanCorrMatrix :: StanType ESqMat
  StanCholeskyFactorCorr :: StanType ESqMat
  StanCovMatrix :: StanType ESqMat
  StanCholeskyFactorCov :: StanType ESqMat

stanIntArray :: StanType (EArray1 EInt)
stanIntArray = StanArray SS StanInt

stanIndexArray :: StanType EIndexArray
stanIndexArray = stanIntArray

stanTypeName :: StanType t -> Text
stanTypeName = \case
  StanInt -> "int"
  StanReal -> "real"
  StanComplex -> "complex"
  StanArray _ _ -> "array"
  StanVector -> "vector"
  StanOrdered -> "ordered"
  StanPositiveOrdered -> "positive_ordered"
  StanSimplex -> "simplex"
  StanUnitVector -> "unit_vector"
  StanRowVector -> "row_vector"
  StanMatrix -> "matrix"
  StanCorrMatrix -> "corr_matrix"
  StanCholeskyFactorCorr -> "cholesky_factor_corr"
  StanCovMatrix -> "cov_matrix"
  StanCholeskyFactorCov -> "cholesky_factor_cov"

eTypeFromStanType :: StanType t -> EType
eTypeFromStanType = \case
  StanInt -> EInt
  StanReal -> EReal
  StanComplex -> EComplex
  StanArray sn st -> EArray (DT.snatToNat sn) (eTypeFromStanType st)
  StanVector -> ECVec
  StanOrdered -> ECVec
  StanPositiveOrdered -> ECVec
  StanSimplex -> ESimplex
  StanUnitVector -> ECVec
  StanRowVector -> ERVec
  StanMatrix -> EMat
  StanCorrMatrix -> ESqMat
  StanCholeskyFactorCorr -> ESqMat
  StanCovMatrix -> ESqMat
  StanCholeskyFactorCov -> ESqMat

sTypeFromStanType :: StanType t -> SType t
sTypeFromStanType = \case
  StanInt -> SInt
  StanReal -> SReal
  StanComplex -> SComplex
  StanArray sn st -> SArray sn (sTypeFromStanType st)
  StanVector -> SCVec
  StanOrdered -> SCVec
  StanPositiveOrdered -> SCVec
  StanSimplex -> SSimplex
  StanUnitVector -> SCVec
  StanRowVector -> SRVec
  StanMatrix -> SMat
  StanCorrMatrix -> SSqMat
  StanCholeskyFactorCorr -> SSqMat
  StanCovMatrix -> SSqMat
  StanCholeskyFactorCov -> SSqMat

instance TestEquality SType where
  testEquality SVoid SVoid = Just Refl
  testEquality SString SString = Just Refl
  testEquality SBool SBool = Just Refl
  testEquality SInt SInt = Just Refl
  testEquality SReal SReal = Just Refl
  testEquality SComplex SComplex = Just Refl
  testEquality SSimplex SSimplex = Just Refl
  testEquality SCVec SCVec = Just Refl
  testEquality SRVec SRVec = Just Refl
  testEquality SMat SMat = Just Refl
  testEquality SSqMat SSqMat = Just Refl
  testEquality (SArray sn sa) (SArray sm sb) = do
    Refl <- testEquality sa sb
    Refl <- testEquality sn sm
    pure Refl
{-  testEquality (sa :-> sb) (sa' :-> sb') = do
    Refl <- testEquality sa sa'
    Refl <- testEquality sb sb'
    pure Refl
-}
  testEquality _ _ = Nothing


{-
-- possible structure of expressions
data EStructure = EVar | ELit | ECompound | ELookup deriving (Show)

-- EStructure Singleton
data SStructure :: EStructure -> Type where
  SVar :: SStructure EVar
  SLit :: SStructure ELit
  SCompound :: SStructure ECompound
  SLookup :: SStructure ELookup

withStructure :: EStructure -> (forall s.SStructure s -> r) -> r
withStructure EVar k = k SVar
withStructure ELit k = k SLit
withStructure ECompound k = k SCompound
withStructure ELookup k = k SLookup


data Ty = Ty EStructure EType

type family TyStructure (a :: Ty) :: EStructure where
  TyStructure ('Ty s _) = s

type family TyType (a :: Ty) :: EType where
  TyType ('Ty _ et) = et
-}
