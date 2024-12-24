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
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Stan.Language.Types
  (
    module Stan.Language.Types
  , Nat(..)
  , SNat(..)
  )
  where

import Prelude hiding (Nat)

import Data.Type.Equality ((:~:)(Refl), TestEquality(testEquality))
import Data.Type.Nat (Nat(..), SNat(..))
import Data.Type.Bool
import qualified Data.Type.Nat as DT
import Stan.Language.Recursion

import qualified GHC.TypeLits as TE
import GHC.TypeLits (ErrorMessage((:<>:)))
import qualified Text.Show
import qualified Data.GADT.Compare as GC
import qualified Data.GADT.Show as GS

import qualified Data.Text as Text


-- possible types of terms
-- NB: zero dimensional array will be treated as the underlying type
-- NB: Stan does not allow 0- or 1-Tuples. We'll enforce that in the declSpec and
-- explicit construction functions
data EType where
  EVoid :: EType
  EString :: EType
  EBool :: EType
  EInt :: EType
  EReal :: EType
  EComplex :: EType
  ECVec :: EType
  ERVec :: EType
  EMat :: EType
  ESqMat :: EType
  EArray :: Nat -> EType -> EType
  ETuple :: [EType] -> EType
--  (::->) :: EType -> EType -> EType
  deriving stock (Eq, Ord, Show)

-- singleton for a list of arguments
data TypeList :: [EType] -> Type where
  TypeNil :: TypeList '[]
  (::>) :: SType et -> TypeList ets -> TypeList (et ': ets)

infixr 2 ::>

typeListToETypeList :: TypeList ts -> [EType]
typeListToETypeList TypeNil = []
typeListToETypeList (st ::> sts) = sTypeToEType st : typeListToETypeList sts

class GenTypeList (ts :: [EType]) where
  genTypeList :: TypeList ts

instance GenTypeList '[] where
  genTypeList = TypeNil

instance (GenSType t, GenTypeList ts) => GenTypeList (t ': ts)  where
  genTypeList = genSType @t ::> genTypeList @ts

type family AllGenTypes (ts :: [EType]) :: Constraint where
  AllGenTypes '[] = ()
  AllGenTypes (t ': ts) = (GenSType t, AllGenTypes ts)

eqTypeList :: TypeList es -> TypeList es' -> Bool
eqTypeList = go
  where
    go :: TypeList es -> TypeList es' -> Bool
    go TypeNil TypeNil = True
    go (sta ::> as) (stb ::> bs) = case testEquality sta stb of
      Just Refl -> go as bs
      Nothing -> False
    go _ _ = False

instance TestEquality TypeList where
  testEquality TypeNil TypeNil = Just Refl
  testEquality (sta ::> as) (stb ::> bs) = do
    Refl <- testEquality sta stb
    Refl <- testEquality as bs
    pure Refl
  testEquality _ _ = Nothing

typesToList ::  (forall t.SType t -> a) -> TypeList args -> [a]
typesToList _ TypeNil = []
typesToList f (st ::> ats) = f st : typesToList f ats

typeListToTypedListOfTypes :: TypeList args -> TypedList SType args
typeListToTypedListOfTypes TypeNil = TNil
typeListToTypedListOfTypes (st ::> atl) = st :> typeListToTypedListOfTypes atl

typedSTypeListToTypeList :: TypedList SType args -> TypeList args
typedSTypeListToTypeList TNil = TypeNil
typedSTypeListToTypeList (st :> xs) = st ::> typedSTypeListToTypeList xs

-- list of arguments.  Parameterized by an expression type and the list of arguments
data TypedList ::  (EType -> Type) -> [EType] -> Type where
  TNil :: TypedList f '[]
  (:>) :: f et -> TypedList f ets -> TypedList f (et ': ets)

infixr 2 :>

--type family IfSameTypedList (tl1 :: TypedList a ts1) (tl2 :: TypedList a ts2) (c :: k) (d :: k) :: k where
--  IfSameTypedList TNil TNil c _ = c
--  IFSameTypedList (a ': as) (b ': bs) c d =

instance TestEquality a => TestEquality (TypedList a) where
  testEquality TNil TNil = Just Refl
  testEquality (sta :> as) (stb :> bs) = do
    Refl <- testEquality sta stb
    Refl <- testEquality as bs
    pure Refl
  testEquality _ _ = Nothing

instance HFunctor TypedList where
  hfmap nat = \case
    TNil -> TNil
    (:>) g al -> nat g :> hfmap nat al

instance HTraversable TypedList where
  htraverse natM = \case
    TNil -> pure TNil
    (:>) aet al -> (:>) <$> natM aet <*> htraverse natM al
  hmapM = htraverse

class GenTypedList (ts :: [EType]) where
  genTypedList :: TypedList SType ts

instance GenTypedList '[] where
  genTypedList :: TypedList SType '[]
  genTypedList = TNil

instance (GenSType t, GenTypedList ts) => GenTypedList (t ': ts)  where
  genTypedList = genSType @t :> genTypedList @ts

-- This is fun! Fold a typed list using a function of it's held data and the coresponding STypes
foldTypedList :: forall a b ts . AllGenTypes ts
              => (forall x. a x -> SType x -> b -> b)
              -> b
              -> TypedList a ts
              -> b
foldTypedList f = go
  where
    go :: forall ts' . AllGenTypes ts' => b -> TypedList a ts' -> b
    go b TNil = b
    go b (a :> as) = go (f a genSType b) as

foldTypedList' :: forall a b ts . (forall x. a x -> b -> b) -> b -> TypedList a ts -> b
foldTypedList' f = go
  where
    go :: forall ts' . b -> TypedList a ts' -> b
    go b TNil = b
    go b (a :> as) = go (f a b) as


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
instance GenEType ECVec where genEType = ECVec
instance GenEType ERVec where genEType = ERVec
instance GenEType EMat where genEType = EMat
instance GenEType ESqMat where genEType = ESqMat
instance (DT.SNatI n, GenEType t) => GenEType (EArray n t) where genEType = EArray (DT.snatToNat $ DT.snat @n) (genEType @t)
instance GenTypedList ts => GenEType (ETuple ts) where genEType = ETuple $ typeListToETypeList $ typedSTypeListToTypeList $ genTypedList @ts

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

type E2Tuple :: EType -> EType -> EType
type E2Tuple t1 t2 = ETuple [t1, t2]

type E3Tuple :: EType -> EType -> EType -> EType
type E3Tuple t1 t2 t3 = ETuple [t1, t2, t3]

data Dict c where
  Dict :: c => Dict c

-- A mechanism to limit the types we can use in functions via a constraint
type TypeOneOf et ets = TypeOneOf' et ets (TypeMember et ets)

type family TypeOneOf' (et :: EType) (ets :: [EType]) (mem :: Bool) :: Constraint where
  TypeOneOf' et ets 'True = ()
  TypeOneOf' et ets 'False = TE.TypeError (TE.ShowType et :<>: TE.Text " is not a member of " :<>: TE.ShowType ets)

type family TypeMember (et :: EType) (ets :: [EType]) :: Bool where
  TypeMember t '[] = False
  TypeMember t (t ': ts) = True
  TypeMember t (t' ': ts) = TypeMember t ts

type family TypeSubset (ets1 :: [EType]) (ets2 :: [EType]) :: Bool where
  TypeSubset '[] _ = True
  TypeSubset (t ': ts) ts' = TypeMember t ts' && TypeSubset ts ts'


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
  ScalarType ECVec = EReal
  ScalarType ERVec = EReal
  ScalarType EMat = EReal
  ScalarType ESqMat = EReal
  ScalarType EReal = EReal
  ScalarType EInt = EInt
  ScalarType EComplex = EComplex
  ScalarType (ETuple '[]) = TE.TypeError (TE.Text "ScalarType: 0-Tuple has no scalar type and is not allowed!")
  ScalarType (ETuple '[e]) = TE.TypeError (TE.Text "ScalarType: 1-Tuple is not allowed!")
  ScalarType (ETuple es) = TE.TypeError (TE.Text "ScalarType: n-Tuple has no scalar type!")
  ScalarType a = TE.TypeError (TE.Text "ScalarType: " TE.:<>: TE.ShowType a TE.:<>: TE.Text " has no scalar type")

type family IsContainer (t :: EType) :: Constraint where
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
  SCVec :: SType ECVec
  SRVec :: SType ERVec
  SMat :: SType EMat
  SSqMat :: SType ESqMat
  SArray :: SNat n -> SType t -> SType (EArray n t)
  STuple :: TypedList SType ts -> SType (ETuple ts)
--  (:->) :: SType t -> SType t' -> SType (t ::-> t')

--extendTuple :: SType t -> SType (ETuple ts) -> SType (ETuple (t ': ts))
--extendTuple st (STuple tl) = STuple (st :> tl)

class GenSType (e :: EType) where
  genSType :: SType e

instance GenSType EVoid where genSType = SVoid
instance GenSType EString where genSType = SString
instance GenSType EBool where genSType = SBool
instance GenSType EInt where genSType = SInt
instance GenSType EReal where genSType = SReal
instance GenSType EComplex where genSType = SComplex
instance GenSType ECVec where genSType = SCVec
instance GenSType ERVec where genSType = SRVec
instance GenSType EMat where genSType = SMat
instance GenSType ESqMat where genSType = SSqMat
instance (DT.SNatI n, GenSType t) => GenSType (EArray n t) where genSType = SArray DT.snat (genSType @t)
instance (GenTypedList ts, AllGenTypes ts) => GenSType (ETuple ts) where genSType = STuple $ genTypedList @ts
--instance (GenSType ta, GenSType tb) => GenSType (ta ::-> tb) where genSType = genSType @ta :-> genSType @tb

type SArray1 t = SType (EArray (S Z) t)

type SIntArray = SArray1 EInt

sIntArray :: SIntArray
sIntArray = SArray SS SInt

sIndexArray :: SType EIndexArray
sIndexArray = sIntArray

s2Tuple :: SType t1 -> SType t2 -> SType (ETuple [t1,t2])
s2Tuple s1 s2 = STuple (s1 :> s2 :> TNil)

s3Tuple :: SType t1 -> SType t2 -> SType t3 -> SType (ETuple [t1, t2, t3])
s3Tuple s1 s2 s3 = STuple (s1 :> s2 :> s3 :> TNil)

instance Show (SType t) where
  show x = "SType: " <> show (sTypeToEType x)

instance GS.GShow SType where gshowsPrec = GS.defaultGshowsPrec

instance Eq (SType t) where
  SVoid == SVoid = True
  SString == SString = True
  SBool == SBool = True
  SInt == SInt = True
  SReal == SReal = True
  SComplex == SComplex = True
  SCVec == SCVec = True
  SRVec == SRVec = True
  SMat == SMat = True
  SSqMat == SSqMat = True
  SArray n st == SArray n' st' = (DT.snatToNat n == DT.snatToNat n') && (st == st')
  STuple ts == STuple ts' = typedSTypeListToTypeList ts `eqTypeList` typedSTypeListToTypeList ts'
--  sa :-> sb == sa' :-> sb' = (sa == sa') && (sb == sb')


sTypeToEType :: SType t -> EType
sTypeToEType = \case
  SVoid -> EVoid
  SString -> EString
  SBool -> EBool
  SInt -> EInt
  SReal -> EReal
  SComplex -> EComplex
  SCVec -> ECVec
  SRVec -> ERVec
  SMat -> EMat
  SSqMat -> ESqMat
  SArray sn st -> case DT.snatToNat sn of
    Z -> sTypeToEType st
    S n -> EArray (S n) $ sTypeToEType st
  STuple ts -> ETuple $ typeListToETypeList $ typedSTypeListToTypeList ts
--  sa :-> sb -> sTypeToEType sa ::-> sTypeToEType sb

withSType :: forall r . EType -> (forall t. SType t -> r) -> r
withSType EVoid k = k SVoid
withSType EString k = k SString
withSType EBool k = k SBool
withSType EInt k = k SInt
withSType EReal k = k SReal
withSType EComplex k = k SComplex
withSType ERVec k = k SRVec
withSType ECVec k = k SCVec
withSType EMat k = k SMat
withSType ESqMat k = k SSqMat
withSType (EArray n t) k = DT.reify n f
  where
    f :: forall n. DT.SNatI n => Proxy n -> r
    f _ = withSType t $ \st -> k (SArray (DT.snat @n) st)
withSType (ETuple []) k = k (STuple TNil)
withSType (ETuple (et : ets)) k =
  withSType et
  $ \ste -> withSType (ETuple ets)
            $ \case
                (STuple sts) -> k (STuple $ ste :> sts)
                _ -> error "withSType (ETuple es): Impossible case!"
--withSType (a ::-> b) k = withSType a $ \sa -> withSType b $ \sb -> k (sa :-> sb)



sTypeName :: SType t -> Text
sTypeName = \case
  SVoid -> "void"
  SString -> "string"
  SBool -> "bool"
  SInt -> "int"
  SReal -> "real"
  SComplex -> "complex"
  SCVec -> "vector"
  SRVec -> "row_vector"
  SMat -> "matrix"
  SSqMat -> "matrix"
  SArray _ _ -> "array" --FIXME
  STuple ts -> "(" <> Text.intercalate ", " (reverse (foldTypedList' (\st tl -> sTypeName st : tl) [] ts)) <> ")"
--  (:->) _ _ -> "funcApply"

data StanType :: EType -> Type where
  StanInt :: StanType EInt
  StanReal :: StanType EReal
  StanComplex :: StanType EComplex
  StanArray :: SNat n -> StanType et -> StanType (EArray n et)
  StanVector :: StanType ECVec
  StanOrdered :: StanType ECVec
  StanPositiveOrdered :: StanType ECVec
  StanSimplex :: StanType ECVec -- was ESimplex
  StanUnitVector :: StanType ECVec
  StanRowVector :: StanType ERVec
  StanMatrix :: StanType EMat
  StanSqMatrix :: StanType ESqMat
  StanCorrMatrix :: StanType ESqMat
  StanCholeskyFactorCorr :: StanType ESqMat
  StanCovMatrix :: StanType ESqMat
  StanCholeskyFactorCov :: StanType ESqMat
  StanTuple :: TypedList StanType ts -> StanType (ETuple ts)

stanIntArray :: StanType (EArray1 EInt)
stanIntArray = StanArray SS StanInt

stanIndexArray :: StanType EIndexArray
stanIndexArray = stanIntArray

stan2Tuple :: StanType e1 -> StanType e2 -> StanType (ETuple [e1, e2])
stan2Tuple st1 st2 = StanTuple (st1 :> st2 :> TNil)

stan3Tuple :: StanType e1 -> StanType e2 -> StanType e3 -> StanType (ETuple [e1, e2, e3])
stan3Tuple st1 st2 st3 = StanTuple (st1 :> st2 :> st3 :> TNil)

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
  StanSqMatrix -> "matrix"
  StanMatrix -> "matrix"
  StanCorrMatrix -> "corr_matrix"
  StanCholeskyFactorCorr -> "cholesky_factor_corr"
  StanCovMatrix -> "cov_matrix"
  StanCholeskyFactorCov -> "cholesky_factor_cov"
  StanTuple ts -> "tuple("
                  <> Text.intercalate ", " (reverse (foldTypedList' (\st ts' -> stanTypeName st : ts') [] ts))
                  <> ")"

eTypeFromStanType :: StanType t -> EType
eTypeFromStanType = \case
  StanInt -> EInt
  StanReal -> EReal
  StanComplex -> EComplex
  StanArray sn st -> EArray (DT.snatToNat sn) (eTypeFromStanType st)
  StanVector -> ECVec
  StanOrdered -> ECVec
  StanPositiveOrdered -> ECVec
  StanSimplex -> ECVec --ESimplex
  StanUnitVector -> ECVec
  StanRowVector -> ERVec
  StanMatrix -> EMat
  StanSqMatrix -> ESqMat
  StanCorrMatrix -> ESqMat
  StanCholeskyFactorCorr -> ESqMat
  StanCovMatrix -> ESqMat
  StanCholeskyFactorCov -> ESqMat
  StanTuple sts -> ETuple $ reverse $ foldTypedList' (\st ets -> eTypeFromStanType st : ets) [] sts

sTypeFromStanType :: StanType t -> SType t
sTypeFromStanType = \case
  StanInt -> SInt
  StanReal -> SReal
  StanComplex -> SComplex
  StanArray sn st -> SArray sn (sTypeFromStanType st)
  StanVector -> SCVec
  StanOrdered -> SCVec
  StanPositiveOrdered -> SCVec
  StanSimplex -> SCVec --SSimplex
  StanUnitVector -> SCVec
  StanRowVector -> SRVec
  StanMatrix -> SMat
  StanSqMatrix -> SSqMat
  StanCorrMatrix -> SSqMat
  StanCholeskyFactorCorr -> SSqMat
  StanCovMatrix -> SSqMat
  StanCholeskyFactorCov -> SSqMat
  StanTuple ts -> STuple $ hfmap sTypeFromStanType ts

instance TestEquality SType where
  testEquality SVoid SVoid = Just Refl
  testEquality SString SString = Just Refl
  testEquality SBool SBool = Just Refl
  testEquality SInt SInt = Just Refl
  testEquality SReal SReal = Just Refl
  testEquality SComplex SComplex = Just Refl
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
  testEquality (STuple TNil) (STuple TNil) = pure Refl
  testEquality (STuple (a :> as)) (STuple (b :> bs)) = do
    Refl <- testEquality a b
    Refl <- testEquality (STuple as) (STuple bs)
    pure Refl
  testEquality _ _ = Nothing

instance GC.GEq SType where
  geq SVoid SVoid = Just Refl
  geq SString SString = Just Refl
  geq SBool SBool = Just Refl
  geq SInt SInt = Just Refl
  geq SReal SReal = Just Refl
  geq SComplex SComplex = Just Refl
  geq SCVec SCVec = Just Refl
  geq SRVec SRVec = Just Refl
  geq SMat SMat = Just Refl
  geq SSqMat SSqMat = Just Refl
  geq (SArray sn sa) (SArray sm sb) = do
    Refl <- GC.geq sa sb
    Refl <- GC.geq sn sm
    pure Refl
  geq  (STuple (a :> as)) (STuple (b :> bs)) = do
    Refl <- testEquality a b
    Refl <- testEquality (STuple as) (STuple bs)
    pure Refl
  geq _ _ = Nothing


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
