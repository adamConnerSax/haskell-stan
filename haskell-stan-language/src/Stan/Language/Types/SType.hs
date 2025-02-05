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
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Stan.Language.Types.SType
  (
    SType(..)
  , AllGenSTypes
  , GenSType(..)
  , GenSTypeList(..)
  , STypeList
  , sTypeName
  , sTypedFoldTypedList
  , sTypeToEType
  , sIndexArray
  )
  where

import Prelude hiding (Nat)

import qualified Stan.Language.Types.EType as SLTE
import qualified Stan.Language.Types.TypedList as SLTT

import Data.Type.Equality ((:~:)(Refl), TestEquality(testEquality))
import Data.Type.Nat (Nat(..), SNat(..))
import qualified Data.Type.Nat as DT
import qualified Text.Show
import qualified Data.GADT.Compare as GC
import qualified Data.GADT.Show as GS

import qualified Data.Text as Text

-- EType singleton
data SType :: SLTE.EType -> Type where
  SVoid :: SType SLTE.EVoid
  SString :: SType SLTE.EString
  SBool :: SType SLTE.EBool
  SInt :: SType SLTE.EInt
  SReal :: SType SLTE.EReal
  SComplex :: SType SLTE.EComplex
  SCVec :: SType SLTE.ECVec
  SRVec :: SType SLTE.ERVec
  SMat :: SType SLTE.EMat
  SSqMat :: SType SLTE.ESqMat
  SArray :: SNat n -> SType t -> SType (SLTE.EArray n t)
  STuple :: SLTT.TypedList SType ts -> SType (SLTE.ETuple ts)

type family AllGenSTypes (ts :: [SLTE.EType]) :: Constraint where
  AllGenSTypes '[] = ()
  AllGenSTypes (t ': ts) = (GenSType t, AllGenSTypes ts)

class GenSType (e :: SLTE.EType) where
  genSType :: SType e

type STypeList = SLTT.TypedList SType

_oneSType :: SType et -> STypeList '[et]
_oneSType st = st SLTT.:> SLTT.TNil

class GenSTypeList (ts :: [SLTE.EType]) where
  genSTypeList :: STypeList ts

instance GenSTypeList '[] where
  genSTypeList :: STypeList '[]
  genSTypeList = SLTT.TNil

instance (GenSType t, GenSTypeList ts) => GenSTypeList (t ': ts)  where
  genSTypeList = genSType @t SLTT.:> genSTypeList @ts

instance GenSType SLTE.EVoid where genSType = SVoid
instance GenSType SLTE.EString where genSType = SString
instance GenSType SLTE.EBool where genSType = SBool
instance GenSType SLTE.EInt where genSType = SInt
instance GenSType SLTE.EReal where genSType = SReal
instance GenSType SLTE.EComplex where genSType = SComplex
instance GenSType SLTE.ECVec where genSType = SCVec
instance GenSType SLTE.ERVec where genSType = SRVec
instance GenSType SLTE.EMat where genSType = SMat
instance GenSType SLTE.ESqMat where genSType = SSqMat
instance (DT.SNatI n, GenSType t) => GenSType (SLTE.EArray n t) where genSType = SArray DT.snat (genSType @t)
instance (GenSTypeList ts, AllGenSTypes ts) => GenSType (SLTE.ETuple ts) where genSType = STuple $ genSTypeList @ts

type SArray1 t = SType (SLTE.EArray (S Z) t)

type SIntArray = SArray1 SLTE.EInt

sIntArray :: SIntArray
sIntArray = SArray SS SInt

sIndexArray :: SType SLTE.EIndexArray
sIndexArray = sIntArray

_s2Tuple :: SType t1 -> SType t2 -> SType (SLTE.ETuple [t1,t2])
_s2Tuple s1 s2 = STuple (s1 SLTT.:> s2 SLTT.:> SLTT.TNil)

_s3Tuple :: SType t1 -> SType t2 -> SType t3 -> SType (SLTE.ETuple [t1, t2, t3])
_s3Tuple s1 s2 s3 = STuple (s1 SLTT.:> s2 SLTT.:> s3 SLTT.:> SLTT.TNil)

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
  STuple ts == STuple ts' = ts `SLTT.eqTypedList` ts'

sTypeListToETypeList :: STypeList ts -> [SLTE.EType]
sTypeListToETypeList SLTT.TNil = []
sTypeListToETypeList (st SLTT.:> sts) = sTypeToEType st : sTypeListToETypeList sts

-- This is fun! Fold a typed list using a function of it's held data and the coresponding STypes
sTypedFoldTypedList :: forall a b ts . AllGenSTypes ts
                    => (forall x. a x -> SType x -> b -> b)
                    -> b
                    -> SLTT.TypedList a ts
                    -> b
sTypedFoldTypedList f = go
  where
    go :: forall ts' . AllGenSTypes ts' => b -> SLTT.TypedList a ts' -> b
    go b SLTT.TNil = b
    go b (a SLTT.:> as) = go (f a genSType b) as

class GenEType (e :: SLTE.EType) where
  genEType :: SLTE.EType

instance GenEType SLTE.EVoid where genEType = SLTE.EVoid
instance GenEType SLTE.EString where genEType = SLTE.EString
instance GenEType SLTE.EBool where genEType = SLTE.EBool
instance GenEType SLTE.EInt where genEType = SLTE.EInt
instance GenEType SLTE.EReal where genEType = SLTE.EReal
instance GenEType SLTE.EComplex where genEType = SLTE.EComplex
instance GenEType SLTE.ECVec where genEType = SLTE.ECVec
instance GenEType SLTE.ERVec where genEType = SLTE.ERVec
instance GenEType SLTE.EMat where genEType = SLTE.EMat
instance GenEType SLTE.ESqMat where genEType = SLTE.ESqMat
instance (DT.SNatI n, GenEType t) => GenEType (SLTE.EArray n t) where genEType = SLTE.EArray (DT.snatToNat $ DT.snat @n) (genEType @t)
instance GenSTypeList ts => GenEType (SLTE.ETuple ts) where genEType = SLTE.ETuple $ sTypeListToETypeList $ genSTypeList @ts


sTypeToEType :: SType t -> SLTE.EType
sTypeToEType = \case
  SVoid -> SLTE.EVoid
  SString -> SLTE.EString
  SBool -> SLTE.EBool
  SInt -> SLTE.EInt
  SReal -> SLTE.EReal
  SComplex -> SLTE.EComplex
  SCVec -> SLTE.ECVec
  SRVec -> SLTE.ERVec
  SMat -> SLTE.EMat
  SSqMat -> SLTE.ESqMat
  SArray sn st -> case DT.snatToNat sn of
    Z -> sTypeToEType st
    S n -> SLTE.EArray (S n) $ sTypeToEType st
  STuple ts -> SLTE.ETuple $ sTypeListToETypeList ts

{-
withSType :: forall r . SLTE.EType -> (forall t. SType t -> r) -> r
withSType SLTE.EVoid k = k SVoid
withSType SLTE.EString k = k SString
withSType SLTE.EBool k = k SBool
withSType SLTE.EInt k = k SInt
withSType SLTE.EReal k = k SReal
withSType SLTE.EComplex k = k SComplex
withSType SLTE.ERVec k = k SRVec
withSType SLTE.ECVec k = k SCVec
withSType SLTE.EMat k = k SMat
withSType SLTE.ESqMat k = k SSqMat
withSType (SLTE.EArray n t) k = DT.reify n f
  where
    f :: forall n. DT.SNatI n => Proxy n -> r
    f _ = withSType t $ \st -> k (SArray (DT.snat @n) st)
withSType (SLTE.ETuple []) k = k (STuple SLTT.TNil)
withSType (SLTE.ETuple (et : ets)) k =
  withSType et
  $ \ste -> withSType (SLTE.ETuple ets)
            $ \case
                (STuple sts) -> k (STuple $ ste SLTT.:> sts)
                _ -> error "withSType (ETuple es): Impossible case!"
-}

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
  STuple ts -> "tuple(" <> Text.intercalate ", " (reverse (SLTT.foldTypedList (\st tl -> sTypeName st : tl) [] ts)) <> ")"

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
  testEquality (STuple SLTT.TNil) (STuple SLTT.TNil) = pure Refl
  testEquality (STuple (a SLTT.:> as)) (STuple (b SLTT.:> bs)) = do
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
  geq  (STuple (a SLTT.:> as)) (STuple (b SLTT.:> bs)) = do
    Refl <- testEquality a b
    Refl <- testEquality (STuple as) (STuple bs)
    pure Refl
  geq _ _ = Nothing
