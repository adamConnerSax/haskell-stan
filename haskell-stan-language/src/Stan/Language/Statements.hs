{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Stan.Language.Statements
  (
    module Stan.Language.Statements
  )
  where

import qualified Stan.Language.Recursion as SLR
import Stan.Language.Expressions
    ( functionE,
      intE,
      namedE,
      namedSizeE,
      ExprList,
      IndexKey,
      VarName,
      IntE,
      LExpr,
      UExpr )
import Stan.Language.Types
    ( sTypeFromStanType,
      Nat(..),
      SNat,
      EIndexArray,
      EType(EInt, EBool, EArray, ESqMat, EMat, ERVec, ECVec, EComplex,
            EReal),
      GenSType(..),
      SType(SInt),
      ScalarType,
      StanType(..),
      sTypeName)
import Stan.Language.TypedList
    ( oneTyped,
      typeListToTypedListOfTypes,
      zipTypedListsWith,
      GenTypeList,
      SameTypeList,
      SameTypedListToVecF,
      TypedList(..),
      VecToSameTypedListF(..) )
import Stan.Language.Indexing
    ( Vec(..),
      DeclDimension,
      Sliced,
      N0,
      DeclIndexVecF(DeclIndexVecF),
      N1,
      s1,
      N2,
      s2 )
import Stan.Language.Operations
    ( BinaryResultT,
      BinaryOp(BAdd, BDivide, BMultiply, BSubtract),
      SBinaryOp(SDivide, SAdd, SSubtract, SMultiply) )
import Stan.Language.Functions
    ( Density,
      Function,
      FuncArg,
      funcArgName,
      functionArgTypes,
      simpleFunction )
--import Stan.Language.StanFunctions

import qualified Data.Vec.Lazy as Vec
import qualified Data.Type.Nat as DT
import Data.Type.Nat (SNatI)
import Data.Type.Equality (type (:~:)(..), gcastWith)
import Control.Monad.Writer.Strict as W

import Prelude hiding (Nat)
import Relude.Extra
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as Map
import Data.Type.Equality (type (:~:)(..))
import qualified Data.Some as Some
import qualified Data.Functor.Foldable as RS
--import qualified Stan.ModelBuilder.Expressions as SB

type StanName = Text

type VecToTListC f n = VecToSameTypedListF f EInt n
type TListToVecC f n = SameTypedListToVecF f EInt n

--type VecToTListAC n t = VecToSameTypedListF UExpr EInt (n `DT.Plus` DeclDimension t)

data DeclSpec t where
  DeclSpec :: StanType t -> Vec (DeclDimension t) (UExpr EInt) -> [VarModifier UExpr (ScalarType t)] -> DeclSpec t
  ArraySpec :: (forall f. VecToTListC f n, forall f.TListToVecC f n, GenTypeList (SameTypeList EInt n))
    => SNat (DT.S n) -> Vec (DT.S n) (UExpr EInt) -> DeclSpec t -> DeclSpec (EArray (DT.S n) t)

data NamedDeclSpec t = NamedDeclSpec StanName (DeclSpec t)

declName :: NamedDeclSpec t -> StanName
declName (NamedDeclSpec n _) = n

decl :: NamedDeclSpec t -> DeclSpec t
decl (NamedDeclSpec _ ds) = ds

declType :: DeclSpec t -> StanType t
declType (DeclSpec st _ _) = st
declType (ArraySpec n _ ds) = StanArray n (declType ds)

declDims :: DeclSpec t -> Vec (DeclDimension t) (UExpr EInt)
declDims (DeclSpec _ dims _) = dims
declDims (ArraySpec _ dims ds) = dims Vec.++ declDims ds

declVMS :: DeclSpec t -> [VarModifier UExpr (ScalarType t)]
declVMS (DeclSpec _ _ vms) = vms
declVMS (ArraySpec _ _ ids) = declVMS ids

replaceDeclVMs :: [VarModifier UExpr (ScalarType t)] -> DeclSpec t -> DeclSpec t
replaceDeclVMs vms = \case
  DeclSpec st vdims _-> DeclSpec st vdims vms
  ArraySpec n arrDims ds -> ArraySpec n arrDims (replaceDeclVMs vms ds)

addVMs :: [VarModifier UExpr (ScalarType t)] -> DeclSpec t -> DeclSpec t
addVMs vms' = \case
  DeclSpec st vdims vms -> DeclSpec st vdims (vms <> vms')
  ArraySpec n arrDims ds -> ArraySpec n arrDims (addVMs vms' ds)

intSpec :: DeclSpec EInt
intSpec = DeclSpec StanInt VNil []

realSpec :: DeclSpec EReal
realSpec = DeclSpec StanReal VNil []

complexSpec :: DeclSpec EComplex
complexSpec = DeclSpec StanComplex VNil []

vectorSpec :: UExpr EInt -> DeclSpec ECVec
vectorSpec ie = DeclSpec StanVector (ie ::: VNil) []

rowVectorSpec :: UExpr EInt -> DeclSpec ERVec
rowVectorSpec ie = DeclSpec StanRowVector (ie ::: VNil) []

orderedSpec :: UExpr EInt -> DeclSpec ECVec
orderedSpec ie = DeclSpec StanOrdered (ie ::: VNil) []

positiveOrderedSpec :: UExpr EInt -> DeclSpec ECVec
positiveOrderedSpec ie = DeclSpec StanPositiveOrdered (ie ::: VNil) []

simplexSpec :: UExpr EInt -> DeclSpec ECVec
simplexSpec ie = DeclSpec StanSimplex (ie ::: VNil) []

unitVectorSpec :: UExpr EInt -> DeclSpec ECVec
unitVectorSpec ie = DeclSpec StanUnitVector (ie ::: VNil) []

matrixSpec :: UExpr EInt -> UExpr EInt -> DeclSpec EMat
matrixSpec re ce = DeclSpec StanMatrix (re ::: ce ::: VNil) []

sqMatrixSpec :: UExpr EInt -> DeclSpec ESqMat
sqMatrixSpec ne = DeclSpec StanSqMatrix (ne ::: VNil) []

corrMatrixSpec :: UExpr EInt -> DeclSpec ESqMat
corrMatrixSpec rce = DeclSpec StanCorrMatrix (rce ::: VNil) []

covMatrixSpec :: UExpr EInt -> DeclSpec ESqMat
covMatrixSpec rce = DeclSpec StanCovMatrix (rce ::: VNil) []

choleskyFactorCorrSpec :: UExpr EInt -> DeclSpec ESqMat
choleskyFactorCorrSpec rce = DeclSpec StanCholeskyFactorCorr (rce ::: VNil) []

choleskyFactorCovSpec :: UExpr EInt -> DeclSpec ESqMat
choleskyFactorCovSpec rce = DeclSpec StanCholeskyFactorCov (rce ::: VNil) []

arraySpec :: (forall f.VecToTListC f n, forall f.TListToVecC f n, GenTypeList (SameTypeList EInt n))
          => SNat (DT.S n) -> Vec (DT.S n) (UExpr EInt) -> DeclSpec t -> DeclSpec (EArray (DT.S n) t)
arraySpec = ArraySpec --(DeclSpec t tIndices vms) = DeclSpec (StanArray n t) (arrIndices Vec.++ tIndices) vms

array1Spec :: UExpr EInt -> DeclSpec t -> DeclSpec (EArray N1 t)
array1Spec se = arraySpec s1 (se ::: VNil)

array2Spec ::  UExpr EInt -> UExpr EInt -> DeclSpec t -> DeclSpec (EArray N2 t)
array2Spec i1 i2 = arraySpec s2 (i1 ::: i2 ::: VNil)

intArraySpec :: UExpr EInt -> DeclSpec EIndexArray
intArraySpec se = arraySpec s1 (se ::: VNil) intSpec

-- 1d int array with a lower bount of 1
indexArraySpec :: UExpr EInt -> DeclSpec EIndexArray
indexArraySpec se = arraySpec s1 (se ::: VNil) (addVMs [lowerM $ intE 1] intSpec)

-- 1d int array with a lower bound of 0
countArraySpec :: UExpr EInt -> DeclSpec EIndexArray
countArraySpec se = arraySpec s1 (se ::: VNil) (addVMs [lowerM $ intE 0] intSpec)


-- functions for ease of use and exporting.  Monomorphised to UStmt, etc.
declare' :: Text -> StanType t -> Vec (DeclDimension t) (UExpr EInt) -> [VarModifier UExpr (ScalarType t)] -> UStmt
declare' vn vt iDecls = SDeclare vn vt (DeclIndexVecF iDecls)

declare :: Text -> DeclSpec t -> UStmt
declare vn (DeclSpec st indices vms) = declare' vn st indices vms
declare vn ds@(ArraySpec _ arrDims ids) = declare' vn (declType ds) (arrDims Vec.++ declDims ids) $ declVMS ids

declareN :: NamedDeclSpec t -> UStmt
declareN (NamedDeclSpec n ds) = declare n ds

declareAndAssign' :: Text -> StanType t -> Vec (DeclDimension t) (UExpr EInt) -> [VarModifier UExpr (ScalarType t)] -> UExpr t -> UStmt
declareAndAssign' vn vt iDecls vms = SDeclAssign vn vt (DeclIndexVecF iDecls) vms

declareAndAssign :: Text -> DeclSpec t -> UExpr t -> UStmt
declareAndAssign vn (DeclSpec vt indices vms) = declareAndAssign' vn vt indices vms
declareAndAssign vn ads@(ArraySpec _ arrDims ids) = declareAndAssign' vn (declType ads) (arrDims Vec.++ declDims ids) $ declVMS ids

declareAndAssignN :: NamedDeclSpec t -> UExpr t -> UStmt
declareAndAssignN (NamedDeclSpec vn ds) = declareAndAssign vn ds

addToTarget :: UExpr EReal -> UStmt
addToTarget = STarget

assign :: UExpr t -> UExpr t -> UStmt
assign = SAssign

-- doing it this way avoids using Stans += syntax.  I just expand.
-- to do otherwise I would have to add a constructor to Stmt
opAssign :: (ta ~ BinaryResultT bop ta tb) => SBinaryOp bop -> UExpr ta -> UExpr tb -> UStmt
opAssign = SOpAssign

plusEq, (+=) :: (ta ~ BinaryResultT BAdd ta tb) => UExpr ta -> UExpr tb -> UStmt
plusEq = opAssign SAdd
(+=) = opAssign SAdd

minusEq, (-=) :: (ta ~ BinaryResultT BSubtract ta tb) => UExpr ta -> UExpr tb -> UStmt
minusEq = opAssign SSubtract
(-=) = opAssign SSubtract

timesEq, (*=) :: (ta ~ BinaryResultT BMultiply ta tb) => UExpr ta -> UExpr tb -> UStmt
timesEq = opAssign SMultiply
(*=) = opAssign SMultiply

divEq, (/=) :: (ta ~ BinaryResultT BDivide ta tb) => UExpr ta -> UExpr tb -> UStmt
divEq = opAssign SDivide
(/=) = opAssign SDivide

data DensityWithArgs g where
  DensityWithArgs :: Density g args -> TypedList UExpr args -> DensityWithArgs g

withDWA :: (forall args.Density g args -> TypedList UExpr args -> r) -> DensityWithArgs g -> r
withDWA f (DensityWithArgs d args) = f d args

target :: UExpr EReal -> UStmt
target = STarget

sample :: UExpr t -> Density t args -> TypedList UExpr args -> UStmt
sample = SSample

sampleW, (|~|) :: UExpr t -> DensityWithArgs t  -> UStmt
sampleW ue (DensityWithArgs d al)= SSample ue d al
ue |~| dwa = sampleW ue dwa

type family ForEachSlice (a :: EType) :: EType where
  ForEachSlice EInt = EInt -- required for looping over ranges. But Ick.
  ForEachSlice ECVec = EReal
  ForEachSlice ERVec = EReal
  ForEachSlice EMat = EReal
  ForEachSlice ESqMat = EReal
  ForEachSlice (EArray m t) = Sliced N0 (EArray m t)

data ForType t where
  SpecificNumbered :: UExpr EInt -> UExpr EInt -> ForType EInt
  IndexedLoop :: IndexKey -> ForType EInt
  SpecificIn :: UExpr t -> ForType t
--  IndexedIn :: IndexKey -> UExpr t -> ForType t

data VarAndForType (t :: EType) where
  VarAndForType :: GenSType (ForEachSlice t) => Text -> ForType t -> VarAndForType t

--intVecToLoopVFTs :: Text -> Vec.Vec n IntE -> TypeList VarAndForType

for :: forall t f . (Traversable f, GenSType (ForEachSlice t))
    => Text -> ForType t -> (UExpr (ForEachSlice t) -> f UStmt) -> UStmt
for loopCounter ft bodyF = case ft of
  SpecificNumbered se' ee' -> SFor loopCounter se' ee' $ bodyF (namedE loopCounter SInt)
  IndexedLoop ik -> SFor loopCounter (intE 1) (namedSizeE ik) $ bodyF (namedE loopCounter SInt)
  SpecificIn e -> SForEach loopCounter e $ bodyF loopCounterE
--  IndexedIn _ e -> SForEach loopCounter e $ bodyF loopCounterE
  where
    loopCounterE = namedE loopCounter $ genSType @(ForEachSlice t)

loopOver :: (Traversable f, GenSType (ForEachSlice t))
         => UExpr t -> Text -> (UExpr (ForEachSlice t) -> f UStmt) -> UStmt
loopOver container loopVarName = for loopVarName (SpecificIn container)
{-# INLINEABLE loopOver #-}

ftSized :: UExpr EInt -> ForType EInt
ftSized = SpecificNumbered (intE 1)

loopSized :: Traversable f => UExpr EInt -> Text -> (UExpr EInt -> f UStmt) -> UStmt
loopSized nE loopVarName = for loopVarName $ ftSized nE
{-# INLINEABLE loopSized #-}

type family ForEachSliceArgs (tl :: [EType]) :: [EType] where
  ForEachSliceArgs '[] = '[]
  ForEachSliceArgs (et ': ets) = ForEachSlice et ': ForEachSliceArgs ets

fesaProof0 :: ForEachSliceArgs (SameTypeList t DT.Z) :~: SameTypeList (ForEachSlice t) DT.Z
fesaProof0 = Refl

newtype FESAProof t n
  = FESAProof
    { getFESAProof :: ForEachSliceArgs (SameTypeList t n) :~: SameTypeList (ForEachSlice t) n}

fesaProofI :: forall t n . DT.SNat n -> FESAProof t n
fesaProofI n = DT.withSNat n
               $ DT.induction (FESAProof Refl)
               (\fpn -> FESAProof $ gcastWith (getFESAProof fpn) Refl)
--fesaProofI DT.SS = gcastWith (fesaProofI $ DT.snatToNat ) Refl

vftSized :: Text -> UExpr EInt -> VarAndForType EInt
vftSized lvn = VarAndForType lvn . ftSized

nestedLoops :: Traversable f
  => TypedList VarAndForType ts -> (ExprList (ForEachSliceArgs ts) -> f UStmt) -> UStmt
nestedLoops TNil f = scoped $ f TNil
nestedLoops (VarAndForType vln ft :> TNil) f = for vln ft $ \e -> f (e :> TNil)
nestedLoops (VarAndForType vln ft :> vfts) f =
  let g e es = f (e :> es) in for vln ft
                              $ \e -> [nestedLoops vfts (g e)]

type IntVecVFT (n :: Nat) = TypedList VarAndForType (SameTypeList EInt n)

vecVFT :: forall m . VecToSameTypedListF VarAndForType EInt m => Text -> Vec.Vec m IntE -> IntVecVFT m
vecVFT counterPrefix v =
  let g :: Nat -> IntE -> VarAndForType EInt
      g nt ie = VarAndForType (counterPrefix <> show nt) (SpecificNumbered (intE 1) ie)
  in vecToSameTypedListF g v

intVecLoops :: forall m f . (VecToSameTypedListF VarAndForType EInt m, Traversable f)
            => Text
            -> Vec.Vec m IntE
            -> (ExprList (ForEachSliceArgs (SameTypeList EInt m)) -> f UStmt)
            -> UStmt
intVecLoops counterPrefix v stmtF = nestedLoops (vecVFT counterPrefix v) stmtF

nullS :: UStmt
nullS = SContext Nothing []

ifThen :: UExpr EBool -> UStmt -> UStmt
ifThen ce sTrue = SIfElse ((ce, sTrue) :| []) nullS

ifThenElse :: NonEmpty (UExpr EBool, UStmt) -> UStmt -> UStmt
ifThenElse = SIfElse

while :: Traversable f => UExpr EBool -> f UStmt -> UStmt
while = SWhile

break :: UStmt
break = SBreak

continue :: UStmt
continue = SContinue

function :: Traversable f => Function rt args -> TypedList (FuncArg Text) args -> (TypedList UExpr args -> (f UStmt, UExpr rt)) -> UStmt
function fd argNames bodyF = SFunction fd argNames bodyS ret
  where
    argTypes = typeListToTypedListOfTypes $ functionArgTypes fd
    argExprs = zipTypedListsWith (namedE . funcArgName) argNames argTypes
    (bodyS, ret) = bodyF argExprs

{-
densityFunction :: Traversable f => Density gt args -> TypedList (FuncArg Text) (gt ': args) -> (TypedList UExpr (gt ': args) -> (f UStmt, UExpr EReal)) -> UStmt
densityFunction fd argNames bodyF = SDensity fd argNames bodyS ret
  where
    argTypes = typeListToTypedListOfTypes $ densityFunctionArgTypes fd
    argExprs = zipTypedListsWith (namedE . funcArgName) argNames argTypes
    (bodyS, ret) = bodyF argExprs
-}

simpleFunctionBody :: Function rt pts
                   -> StanName
                   -> (ExprList pts -> DeclSpec rt)
                   -> (UExpr rt -> ExprList pts -> [UStmt])
                   -> ExprList pts
                   -> (NonEmpty UStmt, UExpr rt)
simpleFunctionBody _ n retDSF bF args = let rE = namedE n st in  (declare n (retDSF args) :| bF rE args, rE)
  where
    st = sTypeFromStanType $ declType $ retDSF args

comment :: NonEmpty Text -> UStmt
comment = SComment

profile :: Traversable f => Text -> f UStmt -> UStmt
profile = SProfile

print :: TypedList UExpr args -> UStmt
print = SPrint

reject :: TypedList UExpr args -> UStmt
reject = SReject

scoped :: Traversable f => f UStmt -> UStmt
scoped = SScoped

context :: Traversable f => (IndexLookupCtxt -> IndexLookupCtxt) -> f UStmt -> UStmt
context cf = SContext (Just cf)

insertIndexBinding :: IndexKey -> LExpr EIndexArray -> IndexLookupCtxt -> IndexLookupCtxt
insertIndexBinding k ie (IndexLookupCtxt a b) = IndexLookupCtxt a (Map.insert k ie b)

insertSizeBinding :: IndexKey -> LExpr EInt -> IndexLookupCtxt -> IndexLookupCtxt
insertSizeBinding k ie (IndexLookupCtxt a b) = IndexLookupCtxt (Map.insert k ie a) b

data VarModifier :: (EType -> Type) -> EType -> Type where
  VarLower :: r t -> VarModifier r t
  VarUpper :: r t -> VarModifier r t
  VarOffset :: r t -> VarModifier r t
  VarMultiplier :: r t -> VarModifier r t

lowerM :: UExpr t -> VarModifier UExpr t
lowerM = VarLower

upperM :: UExpr t -> VarModifier UExpr t
upperM = VarUpper

offsetM :: UExpr t -> VarModifier UExpr t
offsetM = VarOffset

multiplierM :: UExpr t -> VarModifier UExpr t
multiplierM = VarMultiplier

newtype CodeWriter a = CodeWriter { unCodeWriter :: W.Writer [UStmt] a } deriving newtype (Functor, Applicative, Monad, W.MonadWriter [UStmt])

data MaybeCW a = NoCW a | NeedsCW (CodeWriter a)

asCW :: MaybeCW a -> CodeWriter a
asCW (NoCW a) = pure a
asCW (NeedsCW cw) = cw

instance Functor MaybeCW where
  fmap f (NoCW a) = NoCW $ f a
  fmap f (NeedsCW cw) = NeedsCW $ fmap f cw

instance Applicative MaybeCW where
  pure = NoCW
  (NoCW f) <*> (NoCW a) = NoCW $ f a
  (NoCW f) <*> (NeedsCW cw) = NeedsCW $ fmap f cw
  (NeedsCW f) <*> (NoCW a) = NeedsCW $ f <*> (pure a)
  (NeedsCW f) <*> (NeedsCW cw) = NeedsCW $ f <*> cw

instance Monad MaybeCW where
  (NoCW a) >>= f = f a
  (NeedsCW cwa) >>= f = NeedsCW $ do
    a <- cwa
    case f a of
      NoCW b -> pure b
      NeedsCW cwb -> cwb

instance W.MonadWriter [UStmt] MaybeCW where
  tell w = NeedsCW $ W.tell w
  listen m = case m of
    NoCW a -> NoCW (a, [])
    NeedsCW cwa -> NeedsCW $ W.listen cwa
  pass m = case m of
    NoCW (a, _) -> NoCW a
    NeedsCW cw -> NeedsCW $ W.pass cw

writerL :: CodeWriter a -> ([UStmt], a)
writerL (CodeWriter w) = (stmts, a)
  where (a, stmts) = W.runWriter w

writerL' :: CodeWriter a -> [UStmt]
writerL' = fst . writerL

addStmt :: UStmt -> CodeWriter ()
addStmt = W.tell . pure

declareW :: Text -> DeclSpec t -> CodeWriter (UExpr t)
declareW t ds = do
  addStmt $ declare t ds
  return $ namedE t (sTypeFromStanType $ declType ds)

declareNW :: NamedDeclSpec t -> CodeWriter (UExpr t)
declareNW nds = do
  addStmt $ declareN nds
  return $ namedE (declName nds) (sTypeFromStanType $ declType $ decl nds)

declareRHSW :: Text -> DeclSpec t -> UExpr t -> CodeWriter (UExpr t)
declareRHSW t ds rhs = do
  addStmt $ declareAndAssign t ds rhs
  return $ namedE t (sTypeFromStanType $ declType ds)

declareRHSNW :: NamedDeclSpec t -> UExpr t -> CodeWriter (UExpr t)
declareRHSNW nds rhs = do
  addStmt $ declareAndAssignN nds rhs
  return $ namedE (declName nds) (sTypeFromStanType $ declType $ decl nds)

{-
asFunction :: ContainerOf v a -> IntE -> UExpr a
asFunction (InnerSliceable c) = \ke -> sliceE s0 ke c
asFunction (Functional f) = f

asVector :: StanName -> ContainerOf ECVec EReal -> CodeWriter VectorE
asVector n (InnerSliceable c) = pure c
-}

instance SLR.HFunctor VarModifier where
  hfmap f = \case
    VarLower x -> VarLower $ f x
    VarUpper x -> VarUpper $ f x
    VarOffset x -> VarOffset $ f x
    VarMultiplier x -> VarMultiplier $ f x

instance SLR.HTraversable VarModifier where
  htraverse nat = \case
    VarLower x -> VarLower <$> nat x
    VarUpper x -> VarUpper <$> nat x
    VarOffset x -> VarOffset <$> nat x
    VarMultiplier x -> VarMultiplier <$> nat x
  hmapM = SLR.htraverse

data StmtBlock = FunctionsStmts
               | DataStmts
               | TDataStmts
               | ParametersStmts
               | TParametersStmts
               | ModelStmts
               | GeneratedQuantitiesStmts

-- Statements
data Stmt :: (EType -> Type) -> Type where
  SDeclare ::  Text -> StanType et -> DeclIndexVecF r et -> [VarModifier r (ScalarType et)] -> Stmt r
  SDeclAssign :: Text -> StanType et -> DeclIndexVecF r et -> [VarModifier r (ScalarType et)] -> r et -> Stmt r
  SAssign :: r t -> r t -> Stmt r
  SOpAssign :: (ta ~ BinaryResultT op ta tb) => SBinaryOp op -> r ta -> r tb -> Stmt r
  STarget :: r EReal -> Stmt r
  SSample :: r st -> Density st args -> TypedList r args -> Stmt r
  SFor :: Traversable f => Text -> r EInt -> r EInt -> f (Stmt r) -> Stmt r
  SForEach :: Traversable f => Text -> r t -> f (Stmt r) -> Stmt r
  SIfElse :: NonEmpty (r EBool, Stmt r) -> Stmt r -> Stmt r -- [(condition, ifTrue)] -> ifAllFalse
  SWhile :: Traversable f => r EBool -> f (Stmt r) -> Stmt r
  SBreak :: Stmt r
  SContinue :: Stmt r
  SFunction :: Traversable f => Function rt args -> TypedList (FuncArg Text) args -> f (Stmt r) -> r rt -> Stmt r
--  SDensity :: Traversable f => Density gt args -> TypedList (FuncArg Text) (gt ': args) -> f (Stmt r) -> r EReal -> Stmt r
  SComment :: Traversable f => f Text -> Stmt r
  SProfile :: Traversable f => Text -> f (Stmt r) -> Stmt r
  SPrint :: TypedList r args -> Stmt r
  SReject :: TypedList r args -> Stmt r
  SScoped :: Traversable f => f (Stmt r) -> Stmt r
  SBlock :: Traversable f => StmtBlock -> f (Stmt r) -> Stmt r
  SContext :: Traversable f => Maybe (IndexLookupCtxt -> IndexLookupCtxt) -> f (Stmt r) -> Stmt r

data StmtF :: (EType -> Type) -> Type -> Type where
  SDeclareF ::  Text -> StanType et -> DeclIndexVecF r et -> [VarModifier r (ScalarType et)] -> StmtF r a
  SDeclAssignF :: Text -> StanType et -> DeclIndexVecF r et -> [VarModifier r (ScalarType et)] -> r et -> StmtF r a
  SAssignF :: r t -> r t -> StmtF r a
  SOpAssignF :: (ta ~ BinaryResultT op ta tb) => SBinaryOp op -> r ta -> r tb -> StmtF r a
  STargetF :: r EReal -> StmtF r a
  SSampleF :: r st -> Density st args -> TypedList r args -> StmtF r a
  SForF :: Traversable f => Text -> r EInt -> r EInt -> f a -> StmtF r a
  SForEachF :: Traversable f => Text -> r t -> f a -> StmtF r a
  SIfElseF :: NonEmpty (r EBool, a) -> a -> StmtF r a -- [(condition, ifTrue)] -> ifAllFalse
  SWhileF :: Traversable f => r EBool -> f a -> StmtF r a
  SBreakF :: StmtF r a
  SContinueF :: StmtF r a
  SFunctionF :: Traversable f => Function rt args -> TypedList (FuncArg Text) args -> f a -> r rt -> StmtF r a
--  SDensityF :: Traversable f => Density gt args -> TypedList (FuncArg Text) (gt ': args) -> f a -> r EReal -> StmtF r a
  SCommentF :: Traversable f => f Text -> StmtF r a
  SProfileF :: Traversable f => Text -> f a -> StmtF r a
  SPrintF :: TypedList r args -> StmtF r a
  SRejectF :: TypedList r args -> StmtF r a
  SScopedF :: Traversable f => f a -> StmtF r a
  SBlockF :: Traversable f => StmtBlock -> f a -> StmtF r a
  SContextF :: Traversable f => Maybe (IndexLookupCtxt -> IndexLookupCtxt) -> f a -> StmtF r a

type instance RS.Base (Stmt f) = StmtF f

type LStmt = Stmt LExpr
type UStmt = Stmt UExpr
type IndexArrayU = UExpr (EArray (S Z) EInt)
type IndexArrayL = LExpr (EArray (S Z) EInt)
type IndexSizeMap = Map IndexKey (LExpr EInt)
type IndexArrayMap = Map IndexKey IndexArrayL
type VarTypeMap = Map VarName (Some.Some SType)

data VarNameCheck = CheckPassed | NameMissing | WrongType Text

checkTypedVar :: VarName -> SType t -> VarTypeMap -> VarNameCheck
checkTypedVar vn st m = case Map.lookup vn m of
  Nothing -> NameMissing
  Just sst -> if Some.mkSome st == sst then CheckPassed else WrongType $ Some.withSome sst (\prevST -> sTypeName prevST)

newtype VarLookupCtxt = VarLookupCtxt (NE.NonEmpty VarTypeMap)

emptyVarLookupCtxt :: VarLookupCtxt
emptyVarLookupCtxt = VarLookupCtxt $ mempty :| []

varLookupMap :: VarLookupCtxt -> VarTypeMap
varLookupMap (VarLookupCtxt vs) = fold vs

enterNewScope :: VarLookupCtxt -> VarLookupCtxt
enterNewScope (VarLookupCtxt (gs :| ls)) = VarLookupCtxt (gs :| mempty : ls)

{-
innerScope :: VarLookupCtxt -> VarTypeMap
innerScope (VarLookupCtxt (gs :| [])) = gs
innerScope (VarLookupCtxt (gs :| is : _)) = is
-}

leaveScope :: VarLookupCtxt -> Maybe VarLookupCtxt
leaveScope (VarLookupCtxt (gs :| [])) = Nothing
leaveSCope (VarLookupCtxt (gs :| _ : os)) = VarLookupCtxt (gs :| os)

insertVarType :: VarName -> SType t -> VarTypeMap -> VarTypeMap
insertVarType vn st = Map.insert vn (Some.mkSome st)

addTypedVarToInnerScope :: VarName -> SType t -> VarLookupCtxt -> VarLookupCtxt
addTypedVarToInnerScope vn st (VarLookupCtxt (gs :| [])) = VarLookupCtxt $ insertVarType vn st gs :| []
addTypedVarToInnerScope vn st (VarLookupCtxt (gs :| is : os)) = VarLookupCtxt $ gs :| insertVarType vn st is : os

addTypedVarInScope :: VarName -> SType t -> VarLookupCtxt -> Maybe VarLookupCtxt
addTypedVarInScope vn st ctxt = mVLC where
  mExists = Map.lookup vn (varLookupMap ctxt)
  mVLC = case mExists of
    Nothing -> Just $ addTypedVarToInnerScope vn st ctxt
    Just _ -> Nothing

array_num_elements :: (SNatI n, GenSType t) => Function EInt '[EArray n t]
array_num_elements = simpleFunction "size" {- any chance this should be num_elements? --als was "inv"?? -}

indexSize :: IndexArrayU -> UExpr EInt
indexSize = functionE array_num_elements . oneTyped

data IndexLookupCtxt = IndexLookupCtxt { sizes :: IndexSizeMap, indexes :: IndexArrayMap }

emptyLookupCtxt :: IndexLookupCtxt
emptyLookupCtxt = IndexLookupCtxt mempty mempty


instance Functor (StmtF f) where
  fmap f x = case x of
    SDeclareF txt st divf vms -> SDeclareF txt st divf vms
    SDeclAssignF txt st divf vms rhse -> SDeclAssignF txt st divf vms rhse
    SAssignF ft ft' -> SAssignF ft ft'
    SOpAssignF op ft ft' -> SOpAssignF op ft ft'
    STargetF f' -> STargetF f'
    SSampleF f_st dis al -> SSampleF f_st dis al
    SForF ctr startE endE body -> SForF ctr startE endE (f <$> body)
    SForEachF ctr fromE body -> SForEachF ctr fromE (f <$> body)
    SIfElseF x1 sf -> SIfElseF (secondF f x1) (f sf)
    SWhileF cond sfs -> SWhileF cond (f <$> sfs)
    SBreakF -> SBreakF
    SContinueF -> SContinueF
    SFunctionF func al sfs re -> SFunctionF func al (f <$> sfs) re
--    SDensityF dens al sfs re -> SDensityF dens al (f <$> sfs) re
    SCommentF t -> SCommentF t
    SProfileF t stmts -> SProfileF t (f <$> stmts)
    SPrintF args -> SPrintF args
    SRejectF args -> SRejectF args
    SScopedF sfs -> SScopedF $ f <$> sfs
    SBlockF bl stmts -> SBlockF bl (f <$> stmts)
    SContextF mf sts -> SContextF mf $  f <$> sts

instance Foldable (StmtF f) where
  foldMap f = \case
    SDeclareF {} -> mempty
    SDeclAssignF {} -> mempty
    SAssignF {} -> mempty
    SOpAssignF {} -> mempty
    STargetF {} -> mempty
    SSampleF {} -> mempty
    SForF _ _ _ body -> foldMap f body
    SForEachF _ _ body -> foldMap f body
    SIfElseF ifConds sf -> foldMap (f . snd) ifConds <> f sf
    SWhileF _ body -> foldMap f body
    SBreakF -> mempty
    SContinueF -> mempty
    SFunctionF _ _ body _ -> foldMap f body
--    SDensityF _ _ body _ -> foldMap f body
    SCommentF _ -> mempty
    SProfileF _ body -> foldMap f body
    SPrintF {} -> mempty
    SRejectF {} -> mempty
    SScopedF body -> foldMap f body
    SBlockF _ body -> foldMap f body
    SContextF _ body -> foldMap f body

instance Traversable (StmtF f) where
  traverse g = \case
    SDeclareF txt st divf vms -> pure $ SDeclareF txt st divf vms
    SDeclAssignF txt st divf vms fet -> pure $ SDeclAssignF txt st divf vms fet
    SAssignF ft ft' -> pure $ SAssignF ft ft'
    SOpAssignF op ft ft' -> pure $ SOpAssignF op ft ft'
    STargetF f -> pure $ STargetF f
    SSampleF f_st dis al -> pure $ SSampleF f_st dis al
    SForF txt f f' sfs -> SForF txt f f' <$> traverse g sfs
    SForEachF txt ft sfs -> SForEachF txt ft <$> traverse g sfs
    SIfElseF x0 sf -> SIfElseF <$> traverse (\(c, s) -> pure ((,) c) <*> g s) x0 <*> g sf
    SWhileF f body -> SWhileF f <$> traverse g body
    SBreakF -> pure SBreakF
    SContinueF -> pure SContinueF
    SFunctionF func al sfs re -> SFunctionF func al <$> traverse g sfs <*> pure re
--    SDensityF dens al sfs re -> SDensityF dens al <$> traverse g sfs <*> pure re
    SCommentF t -> pure $ SCommentF t
    SProfileF t stmts -> SProfileF t <$> traverse g stmts
    SPrintF args -> pure $ SPrintF args
    SRejectF args -> pure $ SRejectF args
    SScopedF sfs -> SScopedF <$> traverse g sfs
    SBlockF bl stmts -> SBlockF bl <$> traverse g stmts
    SContextF mf sfs -> SContextF mf <$> traverse g sfs

instance Functor (RS.Base (Stmt f)) => RS.Recursive (Stmt f) where
  project = \case
    SDeclare txt st divf vms -> SDeclareF txt st divf vms
    SDeclAssign txt st divf vms fet -> SDeclAssignF txt st divf vms fet
    SAssign ft ft' -> SAssignF ft ft'
    SOpAssign op ft ft' -> SOpAssignF op ft ft'
    STarget f -> STargetF f
    SSample f_st dis al -> SSampleF f_st dis al
    SFor txt f f' sts -> SForF txt f f' sts
    SForEach txt ft sts -> SForEachF txt ft sts
    SIfElse x0 st -> SIfElseF x0 st
    SWhile f sts -> SWhileF f sts
    SBreak -> SBreakF
    SContinue -> SContinueF
    SFunction func al sts re -> SFunctionF func al sts re
--    SDensity dens al sts re -> SDensityF dens al sts re
    SComment t -> SCommentF t
    SProfile t body -> SProfileF t body
    SPrint args -> SPrintF args
    SReject args -> SRejectF args
    SScoped sts -> SScopedF sts
    SBlock bl sts -> SBlockF bl sts
    SContext mf sts -> SContextF mf sts

instance Functor (RS.Base (Stmt f)) => RS.Corecursive (Stmt f) where
  embed = \case
    SDeclareF txt st divf vms -> SDeclare txt st divf vms
    SDeclAssignF txt st divf vms fet -> SDeclAssign txt st divf vms fet
    SAssignF ft ft' -> SAssign ft ft'
    SOpAssignF op ft ft' -> SOpAssign op ft ft'
    STargetF f -> STarget f
    SSampleF f_st dis al -> SSample f_st dis al
    SForF txt f f' sts -> SFor txt f f' sts
    SForEachF txt ft sts -> SForEach txt ft sts
    SIfElseF x0 st -> SIfElse x0 st
    SWhileF f sts -> SWhile f sts
    SBreakF -> SBreak
    SContinueF -> SContinue
    SFunctionF func al sts re -> SFunction func al sts re
--    SDensityF dens al sts re -> SDensity dens al sts re
    SCommentF t -> SComment t
    SProfileF t body -> SProfile t body
    SPrintF args -> SPrint args
    SRejectF args -> SReject args
    SScopedF sts -> SScoped sts
    SBlockF bl sts -> SBlock bl sts
    SContextF mf sts -> SContext mf sts

instance SLR.HFunctor StmtF where
  hfmap nat = \case
    SDeclareF txt st divf vms -> SDeclareF txt st (SLR.hfmap nat divf) (fmap (SLR.hfmap nat) vms)
    SDeclAssignF txt st divf vms rhe -> SDeclAssignF txt st (SLR.hfmap nat divf) (fmap (SLR.hfmap nat) vms) (nat rhe)
    SAssignF lhe rhe -> SAssignF (nat lhe) (nat rhe)
    SOpAssignF op lhe rhe -> SOpAssignF op (nat lhe) (nat rhe)
    STargetF rhe -> STargetF (nat rhe)
    SSampleF gst dis al -> SSampleF (nat gst) dis (SLR.hfmap nat al)
    SForF txt se ee body -> SForF txt (nat se) (nat ee) body
    SForEachF txt gt body -> SForEachF txt (nat gt) body
    SIfElseF x0 sf -> SIfElseF (firstF nat x0) sf
    SWhileF g body -> SWhileF (nat g) body
    SBreakF -> SBreakF
    SContinueF -> SContinueF
    SFunctionF func al body re -> SFunctionF func al body (nat re)
--    SDensityF dens al body re -> SDensityF dens al body (nat re)
    SCommentF x -> SCommentF x
    SProfileF x body -> SProfileF x body
    SPrintF args -> SPrintF (SLR.hfmap nat args)
    SRejectF args -> SRejectF (SLR.hfmap nat args)
    SScopedF body -> SScopedF body
    SBlockF bl body -> SBlockF bl body
    SContextF mf body -> SContextF mf body

instance SLR.HTraversable StmtF where
  htraverse natM = \case
    SDeclareF txt st indexEs vms -> SDeclareF txt st <$> SLR.htraverse natM indexEs <*> traverse (SLR.htraverse natM) vms
    SDeclAssignF txt st indexEs vms rhe -> SDeclAssignF txt st <$> SLR.htraverse natM indexEs <*> traverse (SLR.htraverse natM) vms <*> natM rhe
    SAssignF lhe rhe -> SAssignF <$> natM lhe <*> natM rhe
    SOpAssignF op lhe rhe -> SOpAssignF op <$> natM lhe <*> natM rhe
    STargetF re -> STargetF <$> natM re
    SSampleF ste dist al -> SSampleF <$> natM ste <*> pure dist <*> SLR.htraverse natM al
    SForF txt se ee body -> SForF txt <$> natM se <*> natM ee <*> pure body
    SForEachF txt at' body -> SForEachF txt <$> natM at' <*> pure body
    SIfElseF x0 sf -> SIfElseF <$> traverse (\(c, s) -> (,) <$> natM c <*> pure s) x0 <*> pure sf
    SWhileF cond body -> SWhileF <$> natM cond <*> pure body
    SBreakF -> pure SBreakF
    SContinueF -> pure SContinueF
    SFunctionF func al body re -> SFunctionF func al body <$> natM re
--    SDensityF dens al body re -> SDensityF dens al body <$> natM re
    SCommentF x -> pure $ SCommentF x
    SProfileF x body -> pure $ SProfileF x body
    SPrintF args -> SPrintF <$> SLR.htraverse natM args
    SRejectF args -> SRejectF <$> SLR.htraverse natM args
    SScopedF body -> pure $ SScopedF body
    SBlockF bl body -> pure $ SBlockF bl body
    SContextF mf body -> pure $ SContextF mf body
  hmapM = SLR.htraverse
