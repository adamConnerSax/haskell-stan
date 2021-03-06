{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# LANGUAGE StandaloneKindSignatures #-}

module Stan.ModelBuilder.TypedExpressions.Expressions
  (
    module Stan.ModelBuilder.TypedExpressions.Expressions
  )
  where

import qualified Stan.ModelBuilder.TypedExpressions.Recursion as TR
import Stan.ModelBuilder.TypedExpressions.Types
import Stan.ModelBuilder.TypedExpressions.TypedList
import Stan.ModelBuilder.TypedExpressions.Indexing
import Stan.ModelBuilder.TypedExpressions.Operations
import Stan.ModelBuilder.TypedExpressions.Functions
--import qualified Stan.ModelBuilder.Expressions as SME
import Prelude hiding (Nat)
import Relude.Extra
import qualified Data.Map.Strict as Map
import qualified Data.Monoid as Mon
import qualified Data.Vec.Lazy as Vec
import qualified Data.Type.Nat as DT
import qualified Data.GADT.Compare as DT

import Data.Type.Equality ((:~:)(Refl),TestEquality(testEquality))
import Data.GADT.Compare (GEq(geq))
import Data.Typeable (typeRep)

type IndexKey = Text

-- Expressions
data LExprF :: (EType -> Type) -> EType -> Type where
  LNamed :: Text -> SType t -> LExprF r t
  LInt :: Int -> LExprF r EInt
  LReal :: Double -> LExprF r EReal
  LComplex :: Double -> Double -> LExprF r EComplex
  LString :: Text -> LExprF r EString
  LVector :: [Double] -> LExprF r ECVec
  LMatrix :: [Vec n Double] -> LExprF r EMat
  LArray :: NestedVec n (r t) -> LExprF r (EArray n t)
  LIntRange :: Maybe (r EInt) -> Maybe (r EInt) -> LExprF r (EArray (S Z) EInt)  -- NB: unexported since we only use for indexing
  LFunction :: Function rt args -> TypedList r args -> LExprF r rt
  LDensity :: Density st args -> r st -> TypedList r args -> LExprF r EReal -- e.g., binomial_lupmf(st | ns, p)
  LUnaryOp :: SUnaryOp op -> r t -> LExprF r (UnaryResultT op t)
  LBinaryOp :: SBinaryOp op -> r ta -> r tb -> LExprF r (BinaryResultT op ta tb)
  LCond :: r EBool -> r t -> r t -> LExprF r t
  LSlice :: SNat n -> r EInt -> r t -> LExprF r (Sliced n t)
  LIndex :: SNat n -> r (EArray (S Z) EInt) -> r t -> LExprF r (Indexed n t)
--  LLam :: (r ea -> r eb) -> r ea -> LExprF r (ea ::-> eb)
--  deriving (Typeable)
--  LRangeIndex :: SNat n -> Maybe (r EInt) -> Maybe (r EInt) -> r t -> LExprF r (Indexed n t)


type LExpr = TR.IFix LExprF

lNamedE :: Text -> SType t -> LExpr t
lNamedE name  = TR.IFix . LNamed name

namedLIndex :: Text -> LExpr EIndexArray
namedLIndex t = lNamedE t (SArray s1 SInt)

namedLSize :: Text -> LExpr EInt
namedLSize t = lNamedE t SInt

lIntE :: Int -> LExpr EInt
lIntE = TR.IFix . LInt

instance TR.HFunctor LExprF where
  hfmap nat = \case
    LNamed txt st -> LNamed txt st
    LInt n -> LInt n
    LReal x -> LReal x
    LComplex rp ip -> LComplex rp ip
    LString t -> LString t
    LVector xs -> LVector xs
    LMatrix ms -> LMatrix ms
    LArray nv -> LArray (fmap nat nv)
    LIntRange leM ueM -> LIntRange (fmap nat leM) (fmap nat ueM)
    LFunction f al -> LFunction f (TR.hfmap nat al)
    LDensity d st al -> LDensity d (nat st) (TR.hfmap nat al)
    LUnaryOp suo gta -> LUnaryOp suo (nat gta)
    LBinaryOp sbo gta gtb -> LBinaryOp sbo (nat gta) (nat gtb)
    LCond c ifTrue ifFalse -> LCond (nat c) (nat ifTrue) (nat ifFalse)
    LSlice sn g gt -> LSlice sn (nat g) (nat gt)
    LIndex n re e -> LIndex n (nat re) (nat e)
--    LLam f arg -> LLam (nat f) (nat arg)
--    LRangeIndex n le ue e -> LRangeIndex n (fmap nat le) (fmap nat ue) (nat e)


instance TR.HTraversable LExprF where
  htraverse nat = \case
    LNamed txt st -> pure $ LNamed txt st
    LInt n -> pure $ LInt n
    LReal x -> pure $ LReal x
    LComplex x y -> pure $ LComplex x y
    LString t -> pure $ LString t
    LVector xs -> pure $ LVector xs
    LMatrix ms -> pure $ LMatrix ms
    LArray nv -> LArray <$> traverse nat nv
    LIntRange leM ueM -> LIntRange <$> traverse nat leM <*> traverse nat ueM
    LFunction f al -> LFunction f <$> TR.htraverse nat al
    LDensity d st al -> LDensity d <$> nat st <*> TR.htraverse nat al
    LUnaryOp suo ata -> LUnaryOp suo <$> nat ata
    LBinaryOp sbo ata atb -> LBinaryOp sbo <$> nat ata <*> nat atb
    LCond c ifTrue ifFalse -> LCond <$> nat c <*> nat ifTrue <*> nat ifFalse
    LSlice sn a at -> LSlice sn <$> nat a <*> nat at
    LIndex n re e -> LIndex n <$> nat re <*> nat e
--    LLam f arg -> LLam <$> nat f <*> nat arg
--    LRangeIndex n le ue e -> LRangeIndex n <$> traverse nat le <*> traverse nat ue <*> nat e
  hmapM = TR.htraverse

-- UEXpr represents expressions with un-looked-up indices/sizes
data UExprF :: (EType -> Type) -> EType -> Type where
  UL :: LExprF r et -> UExprF r et
  UNamedIndex :: IndexKey -> UExprF r EIndexArray
  UNamedSize :: IndexKey -> UExprF r EInt

type UExpr = TR.IFix UExprF

instance TR.HFunctor UExprF where
  hfmap nat = \case
    UL le -> UL $ TR.hfmap nat le
    UNamedIndex txt -> UNamedIndex txt
    UNamedSize txt -> UNamedSize txt

instance TR.HTraversable UExprF where
  htraverse nat = \case
    UL le -> UL <$> TR.htraverse nat le
    UNamedIndex txt -> pure $ UNamedIndex txt
    UNamedSize txt -> pure $ UNamedSize txt
  hmapM = TR.htraverse


namedE :: Text -> SType t -> UExpr t
namedE name  = TR.IFix . UL . LNamed name

{-
-- we shouldn't export this constructor.
-- You should only be able to make via the function below.
data Var :: EType -> Type where
  Var :: Text -> StanType t -> UExpr t -> Var t

varName :: Var t -> Text
varName (Var n _ _) = n

varStanType :: Var t -> StanType t
varStanType (Var _ x _) = x

varSType :: Var t -> SType t
varSType = sTypeFromStanType . varStanType

varE :: Var t -> UExpr t
varE (Var _ _ ue) = ue

var :: Text -> StanType t -> Var t
var n st = Var n st $ namedE n $ sTypeFromStanType st
-}
intE :: Int -> UExpr EInt
intE = TR.IFix . UL . LInt

realE :: Double -> UExpr EReal
realE = TR.IFix . UL . LReal

complexE :: Double -> Double -> UExpr EComplex
complexE rp ip = TR.IFix $ UL $ LComplex rp ip

stringE :: Text -> UExpr EString
stringE = TR.IFix . UL . LString

vectorE :: [Double] -> UExpr ECVec
vectorE = TR.IFix . UL . LVector

matrixE :: [Vec n Double] -> UExpr EMat
matrixE = TR.IFix . UL . LMatrix

arrayE :: NestedVec n (UExpr t) -> UExpr (EArray n t)
arrayE = TR.IFix . UL . LArray

type ExprList = TypedList UExpr

functionE :: Function rt args -> TypedList UExpr args -> UExpr rt
functionE f al = TR.IFix $ UL $ LFunction f al

densityE :: Density gt args -> UExpr gt -> TypedList UExpr args -> UExpr EReal
densityE d ge al = TR.IFix $ UL $ LDensity d ge al

unaryOpE :: SUnaryOp op -> UExpr t -> UExpr (UnaryResultT op t)
unaryOpE op e = TR.IFix $ UL $ LUnaryOp op e

negateE :: UExpr t -> UExpr (UnaryResultT UNegate t)
negateE = unaryOpE SNegate

binaryOpE :: SBinaryOp op -> UExpr ta -> UExpr tb -> UExpr (BinaryResultT op ta tb)
binaryOpE op ea eb = TR.IFix $ UL $ LBinaryOp op ea eb

plusE :: UExpr ta -> UExpr tb -> UExpr (BinaryResultT BAdd ta tb)
plusE = binaryOpE SAdd

minusE :: UExpr ta -> UExpr tb -> UExpr (BinaryResultT BSubtract ta tb)
minusE = binaryOpE SSubtract

timesE :: UExpr ta -> UExpr tb -> UExpr (BinaryResultT BMultiply ta tb)
timesE = binaryOpE SMultiply

divideE :: UExpr ta -> UExpr tb -> UExpr (BinaryResultT BDivide ta tb)
divideE = binaryOpE SDivide

boolOpE :: SBoolOp op -> UExpr ta -> UExpr tb -> UExpr (BoolResultT op ta tb)
boolOpE bop ea eb = TR.IFix $ UL $ LBinaryOp (SBoolean bop) ea eb

multiOpE :: (t ~ BinaryResultT op t t) => SBinaryOp op -> NonEmpty (UExpr t) -> UExpr t
multiOpE op es = foldl' (binaryOpE op) (head es) (tail es)

condE :: UExpr EBool -> UExpr t -> UExpr t -> UExpr t
condE ce te fe = TR.IFix $ UL $ LCond ce te fe

sliceE :: SNat n -> UExpr EInt -> UExpr t -> UExpr (Sliced n t)
sliceE sn ie e = TR.IFix $ UL $ LSlice sn ie e

indexE :: SNat n -> UExpr EIndexArray -> UExpr t -> UExpr (Indexed n t)
indexE sn ie e = TR.IFix $ UL $ LIndex sn ie e

rangeIndexE :: SNat n -> Maybe (UExpr EInt) -> Maybe (UExpr EInt) -> UExpr t -> UExpr (Indexed n t)
rangeIndexE n leM ueM = indexE n (TR.IFix $ UL $ LIntRange leM ueM)

namedIndexE :: Text -> UExpr EIndexArray
namedIndexE = TR.IFix . UNamedIndex

namedSizeE :: Text -> UExpr EInt
namedSizeE = TR.IFix . UNamedSize

sliceInner :: UExpr t -> UExpr EInt -> UExpr (SliceInnerN (S Z) t)
sliceInner e i = sliceE SZ i e

-- NB: We need the "go" here to add the SNat to the steps so GHC can convince itself that the lengths match up
-- This will yield a compile-time error if we try to index past the end or, same same, index something scalar.
-- That is, if n > Dimension a, this cannot be compiled.
sliceInnerN :: UExpr t -> Vec n (UExpr EInt) -> UExpr (SliceInnerN n t)
sliceInnerN e v = Vec.withDict v $ go e v where
  go :: DT.SNatI m => UExpr u -> Vec m (UExpr EInt) -> UExpr (SliceInnerN m u)
  go = go' DT.snat
  go' :: DT.SNat k -> UExpr a -> Vec k (UExpr EInt) -> UExpr (SliceInnerN k a)
  go' SZ e _ = e
  go' SS e (i ::: v') = go' DT.snat (sliceInner e i) v'

sliceAll :: UExpr t -> Vec (Dimension t) (UExpr EInt) -> UExpr (SliceInnerN (Dimension t) t)
sliceAll = sliceInnerN


-- some type aliases for ergonomics
type IntE = UExpr EInt
type RealE = UExpr EReal
type ArrayE :: EType -> Type
type ArrayE t = UExpr (EArray1 t)
type IntArrayE = ArrayE EInt
type RealArrayE = ArrayE EReal
type VectorE = UExpr ECVec
type MatrixE = UExpr EMat

{-
data ContainerOf v a where
  InnerSliceable :: Sliced N0 v ~ a => UExpr v -> ContainerOf v a
  Functional :: (IntE -> UExpr t) -> ContainerOf EVoid a

type RealContainer = ContainerOf EReal
type IntContainer = ContainerOf EInt
type VecContainer = ContainerOf ECVec
-}

lExprTypeIs :: LExpr t -> SType t' -> Bool
lExprTypeIs le st = case eqLExprType le (lNamedE "" st) of
  Just Refl -> True
  Nothing -> False

eqLExpr :: LExpr ta -> LExpr tb -> Bool
eqLExpr la lb = case eqLExprType la lb of
  Just Refl -> eqLExprOf la lb
  Nothing -> False

-- This returns some false negatives, but will certainly work on identical epxressions
eqLExprType :: LExpr ta -> LExpr tb -> Maybe (ta :~: tb)
eqLExprType = go
  where
    go :: LExpr ta -> LExpr tb -> Maybe (ta :~: tb)
    go (TR.IFix (LNamed _ sta)) (TR.IFix (LNamed _ stb)) = testEquality sta stb
    go (TR.IFix (LInt _)) (TR.IFix (LInt _)) = Just Refl
    go (TR.IFix (LReal _)) (TR.IFix (LReal _)) = Just Refl
    go (TR.IFix (LComplex _ _)) (TR.IFix (LComplex _ _)) = Just Refl
    go (TR.IFix (LString _)) (TR.IFix (LString _)) = Just Refl
    go (TR.IFix (LVector _)) (TR.IFix (LVector _)) = Just Refl
    go (TR.IFix (LMatrix _)) (TR.IFix (LMatrix _)) = Just Refl
    go (TR.IFix (LArray nv)) (TR.IFix (LArray nv')) = do
      Refl <- eqSizeNestedVec nv nv'
      Refl <- go (nestedVecHead nv) (nestedVecHead nv')
      pure Refl
    go (TR.IFix (LIntRange _ _)) (TR.IFix (LIntRange _ _)) = Just Refl
    go (TR.IFix (LFunction (Function _ sta _ _) _)) (TR.IFix (LFunction (Function _ stb _ _) _)) = testEquality sta stb
    go (TR.IFix (LFunction (IdentityFunction sta) _)) (TR.IFix (LFunction (IdentityFunction stb) _)) = testEquality sta stb
    go (TR.IFix (LDensity _ _ _)) (TR.IFix (LDensity _ _ _)) = Just Refl
    go (TR.IFix (LUnaryOp opa ea)) (TR.IFix (LUnaryOp opb eb)) = do
      Refl <- testEquality opa opb
      Refl <- go ea eb
      pure Refl
    go (TR.IFix (LBinaryOp opa lhsa rhsa)) (TR.IFix (LBinaryOp opb lhsb rhsb)) = do
      Refl <- testEquality opa opb
      Refl <- go lhsa lhsb
      Refl <- go rhsa rhsb
      pure Refl
    go (TR.IFix (LCond _ ea _)) (TR.IFix (LCond _ eb _)) = do
      Refl <- go ea eb
      pure Refl
    go (TR.IFix (LIndex sna _ ea)) (TR.IFix (LIndex snb _ eb)) = do
      let eqSNatWith :: DT.SNatI n => DT.SNat m -> Maybe (n :~: m)
          eqSNatWith sm = DT.withSNat sm DT.eqNat
          eqSNat :: DT.SNat n -> DT.SNat m -> Maybe (n :~: m)
          eqSNat sn sm = DT.withSNat sn $ eqSNatWith sm
      Refl <- eqSNat sna snb
      Refl <- go ea eb
      return Refl
    go _ _ = Nothing

eqLExprOf :: LExpr ta -> LExpr ta -> Bool
eqLExprOf = go
  where
    go :: LExpr ta -> LExpr ta -> Bool
    go (TR.IFix (LNamed na _)) (TR.IFix (LNamed nb _)) = na == nb
    go (TR.IFix (LInt n)) (TR.IFix (LInt m)) = n == m
    go (TR.IFix (LReal x)) (TR.IFix (LReal y)) = x == y
    go (TR.IFix (LComplex xr xi)) (TR.IFix (LComplex yr yi)) = xr == yr && xi == yi
    go (TR.IFix (LString sa)) (TR.IFix (LString sb)) = sa == sb
    go (TR.IFix (LVector xs)) (TR.IFix (LVector ys)) = xs == ys
    go (TR.IFix (LMatrix vs)) (TR.IFix (LMatrix vs')) = getAll $ mconcat $ All <$> zipWith eqVec vs vs'
    go (TR.IFix (LArray nv)) (TR.IFix (LArray nv')) = case eqSizeNestedVec nv nv' of
      Just Refl -> eqNestedVec eqLExprOf nv nv'
      Nothing -> False
    go (TR.IFix (LIntRange mla mua)) (TR.IFix (LIntRange mlb mub)) =
      let cm :: Maybe (LExpr EInt) -> Maybe (LExpr EInt) -> Bool
          cm Nothing Nothing = True
          cm (Just a) (Just b) = go a b
          cm _ _ = False
      in cm mla mlb && cm mua mub
    go (TR.IFix (LFunction (Function fna _ ata aRF) ala)) (TR.IFix (LFunction (Function fnb _ atb bRF) alb)) =
      let eqArgs = case testEquality ata atb of -- given lists are same
            Just Refl -> case testEquality (applyTypedListFunctionToTypeList aRF ata) (applyTypedListFunctionToTypeList bRF atb) of -- reqwritten lists are same
              Just Refl -> eqTypedLists go (aRF ala) (aRF alb) -- given args are same
              Nothing -> False
            Nothing -> False
      in fna == fnb && eqArgs
    go (TR.IFix (LFunction (IdentityFunction _) _)) (TR.IFix (LFunction (IdentityFunction _) _)) = True
    go (TR.IFix (LDensity (Density dna gta ata aRF) ga ala)) (TR.IFix (LDensity (Density dnb gtb atb bRF) gb alb)) =
      let eqGivens = case testEquality gta gtb of
            Just Refl -> True
            Nothing -> False
          eqArgs =  case testEquality ata atb of
            Just Refl -> case testEquality (applyTypedListFunctionToTypeList aRF ata) (applyTypedListFunctionToTypeList bRF atb) of -- reqwritten lists are same
              Just Refl -> eqTypedLists go ala alb
              Nothing -> False
            Nothing -> False
      in dna == dnb && eqGivens && eqArgs
    go (TR.IFix (LUnaryOp opa ea)) (TR.IFix (LUnaryOp opb eb)) = case testEquality opa opb of
      Just Refl -> case eqLExprType ea eb of
        Just Refl -> go ea eb
        Nothing -> False
      Nothing -> False
    go (TR.IFix (LBinaryOp opa lhsa rhsa)) (TR.IFix (LBinaryOp opb lhsb rhsb)) = case testEquality opa opb of
      Just Refl -> case eqLExprType lhsa lhsb of
        Just Refl -> case eqLExprType rhsa rhsb of
          Just Refl -> go lhsa lhsb && go rhsa rhsb
          Nothing -> False
        Nothing -> False
      Nothing -> False
    go (TR.IFix (LCond ca lhsa rhsa)) (TR.IFix (LCond cb lhsb rhsb)) = go ca cb && go lhsa lhsb && go rhsa rhsb
    go (TR.IFix (LIndex _ iea ea)) (TR.IFix (LIndex _ ieb eb)) =
      go iea ieb && case eqLExprType ea eb of
                      Just Refl -> go ea eb
                      Nothing -> False
    go _ _ = False

-- This is either very cool or very dangerous
-- replace each lookup with a blank thing of same type just for typechecking purposes
uExprToSameTypeLExpr :: UExpr t -> LExpr t
uExprToSameTypeLExpr = TR.iCata f where
  f :: UExprF LExpr TR.~> LExpr
  f = \case
    UL le -> TR.IFix le
    UNamedIndex _ -> lNamedE "" (SArray s1 SInt)
    UNamedSize _ -> lNamedE "" SInt

exprTypeIs :: UExpr t -> SType t' -> Bool
exprTypeIs ue = lExprTypeIs (uExprToSameTypeLExpr ue)


-- Expression to Expression transformations
{- Can't figure this out! The nested type-family is not resolving and the nats are annoying
   Doing at the term-level.  Which...yuck.
embedSlicesAlg :: forall z.LExprF LExpr z -> LExpr z
embedSlicesAlg x = case x of
  LSlice sn ie (TR.IFix (LIndex sm re e)) ->
    DT.withSNat sn $ DT.withSNat sm $ case DT.cmpNat of
    DT.GEQ -> TR.IFix $ LSlice sn (TR.IFix (LSlice SZ ie re)) e
--    DT.GGT -> LIndex
  x -> TR.IFix x
{-
  where
    embedIf :: _ --forall n m u.SNat n -> SNat m -> LExpr EInt -> LExpr (EArray (S Z) EInt) -> LExpr u -> LExpr (Sliced n u)
    embedIf sn sm ie re e = DT.withSNat sn  $ DT.withSNat sm $ (embedIf' @n @m) ie re e
    embedIf' :: forall n m u.(DT.SNatI n, DT.SNatI m) =>  LExpr EInt -> LExpr (EArray (S Z) EInt) -> LExpr u -> LExpr (Sliced n u)
    embedIf' ie re e = undefined IFix $ case DT.cmpNat of
      DT.GEQ -> LSlice (DT.snat @n) (IFix (LSlice Z ie re)) e
      DT.GGT -> LIndex (DT.snat @m) re (LSlice (DT.snat @n) ie e)
      DT.GLT -> case DT.snat @m of
        DT.SZ -> undefined
        DT.SS -> LIndex DT.snat (LSlice (DT.snat @n) ie e)
-}
-}
{-
plusE :: UExprF ta a -> UExprF tb a -> UExprF (BinaryResultT BAdd ta tb) a
plusE = BinaryOpE SAdd
-}

{-
useVar :: forall r.SME.StanVar -> (forall t.UExpr t -> r) -> r
useVar (SME.StanVar n x) k = case x of
  StanInt -> k $ NamedE n x SInt
  StanReal -> k $ NamedE n x SReal
  StanArray _ st -> toSType (fromStanType st) (k . NamedE n x . SArray)
  StanVector _ -> k $ NamedE n x SCVec
  StanMatrix _ -> k $ NamedE n x SMat
  StanCorrMatrix sd -> k $ NamedE n x SMat
  StanCholeskyFactorCorr sd -> k $ NamedE n x SMat
  StanCovMatrix sd -> k $ NamedE n x SMat
-}
{-
data StanType = StanInt
              | StanReal
              | StanArray [SME.StanDim] StanType
              | StanVector SME.StanDim
              | StanMatrix (SME.StanDim, SME.StanDim)
              | StanCorrMatrix SME.StanDim
              | StanCholeskyFactorCorr SME.StanDim
              | StanCovMatrix SME.StanDim
              deriving (Show, Eq, Ord, Generic)

fromStanType :: StanType -> EType
fromStanType = \case
  StanInt -> EInt
  StanReal -> EReal
  StanArray _ st -> EArray (fromStanType st)
  StanVector _ -> ECVec
  StanMatrix _ -> EMat
  StanCorrMatrix _ -> EMat
  StanCholeskyFactorCorr _ -> EMat
  StanCovMatrix _ -> EMat
-}
{-
class ToEType a where
  toEType :: EType

instance ToEType SInt where
  toEType = EInt
instance ToEType SInt where

  toEType SReal = EReal
  toEType SCVec = ECVec
  toEType SRVec = ERVec
  toEType SMat = EMat
  toEType (SArray st) = EArray (toEType st)
  toEType (sa ::-> sb) = toEType sa :-> toEType sb
-}
{-
  toSType (fromStanType x) f where
  f :: forall u.SType u -> r
  f = case x of
    StanInt -> k $ UNamedE n x SInt
    StanReal -> k $ UNamedE n x SReal
    StanArray _ st -> k $ toSType (fromStanType st) $ UNamedE n x . SArray
    StanVector sd -> _
    StanMatrix x1 -> _
    StanCorrMatrix sd -> _
    StanCholeskyFactorCorr sd -> _
    StanCovMatrix sd -> _
-}

{-
intE :: Int -> UExpr EInt
intE = IntE

realE :: Double -> UExpr EReal
realE = RealE

varE :: SType t -> Text -> UExpr t
varE _ = VarE

plusOpE :: UExpr t -> UExpr (t :-> t)
plusOpE a = FunE ()
-}

{-
instance TR.HFoldable UExprF where
  hfoldMap co = \case
    DeclareEF st divf -> mempty
    NamedEF txt st -> mempty
    IntEF n -> mempty
    RealEF x -> mempty
    ComplexEF x y -> mempty
    BinaryOpEF sbo ata atb -> co ata <> co atb
    SliceEF sn a at -> co a <> co at
    NamedIndexEF txt -> mempty
-}
