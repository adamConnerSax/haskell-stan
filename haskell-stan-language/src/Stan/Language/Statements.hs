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
{-# LANGUAGE UndecidableInstances #-}

module Stan.Language.Statements
  (
    module Stan.Language.Statements
  )
  where

import qualified Stan.Language.Recursion as SLR
import qualified Stan.Language.Statement as SLS
import Stan.Language.Statement (DeclSpec(..))
import qualified Stan.Language.ASTContext as SLA
import qualified Stan.Language.Expression as SLE
import Stan.Language.Expressions
  (intE,
   namedE,
   namedSizeE,
   ExprList,
   IntE)
import Stan.Language.Types
    ( sTypeFromStanType,
      EIndexArray,
      EType(..),
      GenSType(..),
      SType(SInt),
      ScalarType,
      StanType(..),
      TypedList(TNil, (:>)),
      GenSTypeList,
      SameTypeList,
      AllGenSTypes,
      genSTypeList,
      vecToSameTypedListF,
      zipTypedListsWith,
      VecToSameTypedListF,
      VarName,
      FunctionName
    )
import Stan.Language.Indexing
    ( Vec(..),
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
    )

import qualified Data.Vec.Lazy as Vec
import qualified Data.Type.Nat as DT
import Data.Type.Nat (Nat, SNat)
import Data.Type.Equality (type (:~:)(..), gcastWith)

import Prelude hiding (Nat)
--import Relude.Extra
import qualified Data.Map.Strict as Map

data NamedDeclSpec t = NamedDeclSpec VarName (DeclSpec SLE.UExpr t)

declName :: NamedDeclSpec t -> VarName
declName (NamedDeclSpec n _) = n

decl :: NamedDeclSpec t -> DeclSpec SLE.UExpr t
decl (NamedDeclSpec _ ds) = ds

declType :: DeclSpec SLE.UExpr t -> StanType t
declType (ScalarSpec st _) = st
declType (VectorSpec st _ _) = st
declType (MatrixSpec st _ _ _) = st
declType (ArraySpec n _ ds) = StanArray n (declType ds)
declType (TupleSpec ts) = StanTuple $ SLR.hfmap declType ts

declSType :: DeclSpec SLE.UExpr t -> SType t
declSType = sTypeFromStanType . declType

replaceDeclVMs :: SLS.VarModifiers r (ScalarType t) -> DeclSpec r t -> DeclSpec r t
replaceDeclVMs vms = \case
  ScalarSpec st _ -> ScalarSpec st vms
  VectorSpec st l _ -> VectorSpec st l vms
  MatrixSpec st r c _ -> MatrixSpec st r c vms
  ArraySpec n arrDims ds -> ArraySpec n arrDims (replaceDeclVMs vms ds)
  TupleSpec _sts -> error "Can't replace constraints on a tuple. Need to do it one item at a time?" --TupleSpec sts

addVMs :: SLS.VarModifiers r (ScalarType t) -> DeclSpec r t -> DeclSpec r t
addVMs vms' = \case
  ScalarSpec st vms -> ScalarSpec st (vms <> vms')
  VectorSpec st l vms -> VectorSpec st l (vms <> vms')
  MatrixSpec st r c vms -> MatrixSpec st r c (vms <> vms')
  ArraySpec n arrDims ds -> ArraySpec n arrDims (addVMs vms' ds)
  TupleSpec _sts -> error "Can't add constraints to a tuple. Need to do it one item at a time?" --TupleSpec sts

removeVMs :: DeclSpec r t -> DeclSpec r t
removeVMs = \case
  ScalarSpec st _ -> ScalarSpec st SLS.NoModifiers
  VectorSpec st l _ -> VectorSpec st l SLS.NoModifiers
  MatrixSpec st r c _ -> MatrixSpec st r c SLS.NoModifiers
  ArraySpec n arrDims ds -> ArraySpec n arrDims (removeVMs ds)
  TupleSpec sts -> TupleSpec $ SLR.hfmap removeVMs sts


intSpec :: DeclSpec SLE.UExpr EInt
intSpec = ScalarSpec StanInt SLS.NoModifiers

realSpec :: DeclSpec SLE.UExpr EReal
realSpec = ScalarSpec StanReal SLS.NoModifiers

complexSpec :: DeclSpec SLE.UExpr EComplex
complexSpec = ScalarSpec StanComplex SLS.NoModifiers

vectorSpec :: SLE.UExpr EInt -> DeclSpec SLE.UExpr ECVec
vectorSpec ie = VectorSpec StanVector ie SLS.NoModifiers

rowVectorSpec :: SLE.UExpr EInt -> DeclSpec SLE.UExpr ERVec
rowVectorSpec ie = VectorSpec StanRowVector ie SLS.NoModifiers

orderedSpec :: SLE.UExpr EInt -> DeclSpec SLE.UExpr ECVec
orderedSpec ie = VectorSpec StanOrdered ie SLS.NoModifiers

positiveOrderedSpec :: SLE.UExpr EInt -> DeclSpec SLE.UExpr ECVec
positiveOrderedSpec ie = VectorSpec StanPositiveOrdered ie SLS.NoModifiers

simplexSpec :: SLE.UExpr EInt -> DeclSpec SLE.UExpr ECVec
simplexSpec ie = VectorSpec StanSimplex ie SLS.NoModifiers

unitVectorSpec :: SLE.UExpr EInt -> DeclSpec SLE.UExpr ECVec
unitVectorSpec ie = VectorSpec StanUnitVector ie SLS.NoModifiers

matrixSpec :: SLE.UExpr EInt -> SLE.UExpr EInt -> DeclSpec SLE.UExpr EMat
matrixSpec re ce = MatrixSpec StanMatrix re ce SLS.NoModifiers

sqMatrixSpec :: SLE.UExpr EInt -> DeclSpec SLE.UExpr ESqMat
sqMatrixSpec ne = MatrixSpec StanSqMatrix ne ne SLS.NoModifiers

corrMatrixSpec :: SLE.UExpr EInt -> DeclSpec SLE.UExpr ESqMat
corrMatrixSpec rce = MatrixSpec StanCorrMatrix rce rce SLS.NoModifiers

covMatrixSpec :: SLE.UExpr EInt -> DeclSpec SLE.UExpr ESqMat
covMatrixSpec rce = MatrixSpec StanCovMatrix rce rce SLS.NoModifiers

choleskyFactorCorrSpec :: SLE.UExpr EInt -> DeclSpec SLE.UExpr ESqMat
choleskyFactorCorrSpec rce = MatrixSpec StanCholeskyFactorCorr rce rce SLS.NoModifiers

choleskyFactorCovSpec :: SLE.UExpr EInt -> DeclSpec SLE.UExpr ESqMat
choleskyFactorCovSpec rce = MatrixSpec StanCholeskyFactorCov rce rce SLS.NoModifiers

arraySpec :: (forall f.SLS.VecToTListC f n, forall f . SLS.TListToVecC f n, GenSTypeList (SameTypeList EInt n), AllGenSTypes (SameTypeList EInt n))
          => SNat (DT.S n) -> Vec (DT.S n) (SLE.UExpr EInt) -> DeclSpec SLE.UExpr t -> DeclSpec SLE.UExpr (EArray (DT.S n) t)
arraySpec = ArraySpec --(DeclSpec t tIndices vms) = DeclSpec (StanArray n t) (arrIndices Vec.++ tIndices) vms

array1Spec :: SLE.UExpr EInt -> DeclSpec SLE.UExpr t -> DeclSpec SLE.UExpr (EArray N1 t)
array1Spec se = arraySpec s1 (se ::: VNil)

array2Spec ::  SLE.UExpr EInt -> SLE.UExpr EInt -> DeclSpec SLE.UExpr t -> DeclSpec SLE.UExpr (EArray N2 t)
array2Spec i1 i2 = arraySpec s2 (i1 ::: i2 ::: VNil)

intArraySpec :: SLE.UExpr EInt -> DeclSpec SLE.UExpr EIndexArray
intArraySpec se = arraySpec s1 (se ::: VNil) intSpec

-- 1d int array with a lower bount of 1
indexArraySpec :: SLE.UExpr EInt -> DeclSpec SLE.UExpr EIndexArray
indexArraySpec se = arraySpec s1 (se ::: VNil) (addVMs (SLS.Modifiers [lowerM $ intE 1]) intSpec)

-- 1d int array with a lower bound of 0
countArraySpec :: SLE.UExpr EInt -> DeclSpec SLE.UExpr EIndexArray
countArraySpec se = arraySpec s1 (se ::: VNil) (addVMs (SLS.Modifiers [lowerM $ intE 0]) intSpec)

-- arbitrary sized tuple
tupleSpec :: TypedList (DeclSpec SLE.UExpr) ts -> DeclSpec SLE.UExpr (ETuple ts)
tupleSpec = TupleSpec

tuple2Spec :: DeclSpec SLE.UExpr t1 -> DeclSpec SLE.UExpr t2 -> DeclSpec SLE.UExpr (ETuple [t1, t2])
tuple2Spec ds1 ds2 = TupleSpec (ds1 :> ds2 :> TNil)

tuple3Spec :: DeclSpec SLE.UExpr t1 -> DeclSpec SLE.UExpr t2 -> DeclSpec SLE.UExpr t3 -> DeclSpec SLE.UExpr (ETuple [t1, t2, t3])
tuple3Spec ds1 ds2 ds3 = TupleSpec (ds1 :> ds2 :> ds3 :> TNil)


-- functions for ease of use and exporting.  Monomorphised to UStmt, etc.
declare :: Text -> DeclSpec SLE.UExpr t -> SLS.UStmt
declare  = SLS.SDeclare

declareN :: NamedDeclSpec t -> SLS.UStmt
declareN (NamedDeclSpec n ds) = declare n ds

declareAndAssign :: Text -> DeclSpec SLE.UExpr t -> SLE.UExpr t -> SLS.UStmt
declareAndAssign = SLS.SDeclAssign

declareAndAssignN :: NamedDeclSpec t -> SLE.UExpr t -> SLS.UStmt
declareAndAssignN (NamedDeclSpec vn ds) = declareAndAssign vn ds

addToTarget :: SLE.UExpr EReal -> SLS.UStmt
addToTarget = SLS.STarget

assign, (|=|) :: SLE.UExpr t -> SLE.UExpr t -> SLS.UStmt
assign = SLS.SAssign
(|=|) = SLS.SAssign

-- doing it this way avoids using Stans += syntax.  I just expand.
-- to do otherwise I would have to add a constructor to Stmt
opAssign :: (ta ~ BinaryResultT bop ta tb) => SBinaryOp bop -> SLE.UExpr ta -> SLE.UExpr tb -> SLS.UStmt
opAssign = SLS.SOpAssign

plusEq, (+=) :: (ta ~ BinaryResultT BAdd ta tb) => SLE.UExpr ta -> SLE.UExpr tb -> SLS.UStmt
plusEq = opAssign SAdd
(+=) = opAssign SAdd

minusEq, (-=) :: (ta ~ BinaryResultT BSubtract ta tb) => SLE.UExpr ta -> SLE.UExpr tb -> SLS.UStmt
minusEq = opAssign SSubtract
(-=) = opAssign SSubtract

timesEq, (*=) :: (ta ~ BinaryResultT BMultiply ta tb) => SLE.UExpr ta -> SLE.UExpr tb -> SLS.UStmt
timesEq = opAssign SMultiply
(*=) = opAssign SMultiply

divEq, (/=) :: (ta ~ BinaryResultT BDivide ta tb) => SLE.UExpr ta -> SLE.UExpr tb -> SLS.UStmt
divEq = opAssign SDivide
(/=) = opAssign SDivide

data DensityWithArgs g where
  DensityWithArgs :: Density g args -> TypedList SLE.UExpr args -> DensityWithArgs g

withDWA :: (forall args.Density g args -> TypedList SLE.UExpr args -> r) -> DensityWithArgs g -> r
withDWA f (DensityWithArgs d args) = f d args

target :: SLE.UExpr EReal -> SLS.UStmt
target = SLS.STarget

sample :: SLE.UExpr t -> Density t args -> TypedList SLE.UExpr args -> SLS.UStmt
sample = SLS.SSample

sampleW, (|~|) :: SLE.UExpr t -> DensityWithArgs t  -> SLS.UStmt
sampleW ue (DensityWithArgs d al)= SLS.SSample ue d al
ue |~| dwa = sampleW ue dwa

for :: forall t . GenSType (SLS.ForEachSlice t)
    => Text -> SLS.ForType t -> (SLE.UExpr (SLS.ForEachSlice t) -> SLS.UStmt) -> SLS.UStmt
for loopCounter ft bodyF = case ft of
  SLS.SpecificNumbered se' ee' -> scoped $ SLS.SFor loopCounter se' ee' $ bodyF (namedE loopCounter SInt)
  SLS.IndexedLoop ik -> scoped $ SLS.SFor loopCounter (intE 1) (namedSizeE ik) $ bodyF (namedE loopCounter SInt)
  SLS.SpecificIn e -> scoped $ SLS.SForEach loopCounter e $ bodyF loopCounterE
--  IndexedIn _ e -> SForEach loopCounter e $ bodyF loopCounterE
  where
    loopCounterE = namedE loopCounter $ genSType @(SLS.ForEachSlice t)

loopOver :: GenSType (SLS.ForEachSlice t)
         => SLE.UExpr t -> Text -> (SLE.UExpr (SLS.ForEachSlice t) -> SLS.UStmt) -> SLS.UStmt
loopOver container loopVarName = for loopVarName (SLS.SpecificIn container)
{-# INLINEABLE loopOver #-}

ftSized :: SLE.UExpr EInt -> SLS.ForType EInt
ftSized = SLS.SpecificNumbered (intE 1)

loopSized :: SLE.UExpr EInt -> Text -> (SLE.UExpr EInt -> SLS.UStmt) -> SLS.UStmt
loopSized nE loopVarName = for loopVarName $ ftSized nE
{-# INLINEABLE loopSized #-}

type family ForEachSliceArgs (tl :: [EType]) :: [EType] where
  ForEachSliceArgs '[] = '[]
  ForEachSliceArgs (et ': ets) = SLS.ForEachSlice et ': ForEachSliceArgs ets

fesaProof0 :: ForEachSliceArgs (SameTypeList t DT.Z) :~: SameTypeList (SLS.ForEachSlice t) DT.Z
fesaProof0 = Refl

newtype FESAProof t n
  = FESAProof
    { getFESAProof :: ForEachSliceArgs (SameTypeList t n) :~: SameTypeList (SLS.ForEachSlice t) n}

fesaProofI :: forall t n . DT.SNat n -> FESAProof t n
fesaProofI n = DT.withSNat n
               $ DT.induction (FESAProof Refl)
               (\fpn -> FESAProof $ gcastWith (getFESAProof fpn) Refl)
--fesaProofI DT.SS = gcastWith (fesaProofI $ DT.snatToNat ) Refl

vftSized :: Text -> SLE.UExpr EInt -> SLS.VarAndForType EInt
vftSized lvn = SLS.VarAndForType lvn . ftSized

nestedLoops :: TypedList SLS.VarAndForType ts -> (ExprList (ForEachSliceArgs ts) -> SLS.UStmt) -> SLS.UStmt
nestedLoops TNil f = scoped $ f TNil
nestedLoops (SLS.VarAndForType vln ft :> TNil) f = for vln ft $ \e -> f (e :> TNil)
nestedLoops (SLS.VarAndForType vln ft :> vfts) f =
  let g e es = f (e :> es) in for vln ft
                              $ \e -> nestedLoops vfts (g e)

type IntVecVFT (n :: Nat) = TypedList SLS.VarAndForType (SameTypeList EInt n)

vecVFT :: forall m . VecToSameTypedListF SLS.VarAndForType EInt m => Text -> Vec.Vec m IntE -> IntVecVFT m
vecVFT counterPrefix v =
  let g :: Nat -> IntE -> SLS.VarAndForType EInt
      g nt ie = SLS.VarAndForType (counterPrefix <> show nt) (SLS.SpecificNumbered (intE 1) ie)
  in vecToSameTypedListF g v

intVecLoops :: forall m . (VecToSameTypedListF SLS.VarAndForType EInt m)
            => Text
            -> Vec.Vec m IntE
            -> (ExprList (ForEachSliceArgs (SameTypeList EInt m)) -> SLS.UStmt)
            -> SLS.UStmt
intVecLoops counterPrefix v stmtF = nestedLoops (vecVFT counterPrefix v) stmtF

nullS :: SLS.UStmt
nullS = SLS.SContext id

ifThen :: SLE.UExpr EBool -> SLS.UStmt -> SLS.UStmt
ifThen ce sTrue = SLS.SIfElse ((ce, sTrue) :| []) nullS

ifThenElse :: NonEmpty (SLE.UExpr EBool, SLS.UStmt) -> SLS.UStmt -> SLS.UStmt
ifThenElse = SLS.SIfElse

while :: SLE.UExpr EBool -> SLS.UStmt -> SLS.UStmt
while = SLS.SWhile

break :: SLS.UStmt
break = SLS.SBreak

continue :: SLS.UStmt
continue = SLS.SContinue

function :: forall args rt . GenSTypeList args
         => Function rt args -> TypedList (FuncArg Text) args -> (TypedList SLE.UExpr args -> (SLS.UStmt, SLE.UExpr rt)) -> SLS.UStmt
function fd argNames bodyF = scoped $ SLS.SFunction fd argNames $ grouped [bodyS, SLS.SReturn ret]
  where
    argTypes = genSTypeList @args --functionArgTypes fd
    argExprs = zipTypedListsWith (namedE . funcArgName) argNames argTypes
    (bodyS, ret) = bodyF argExprs

simpleFunctionBody :: Function rt pts
                   -> FunctionName
                   -> (ExprList pts -> DeclSpec SLE.UExpr rt)
                   -> (SLE.UExpr rt -> ExprList pts -> [SLS.UStmt])
                   -> ExprList pts
                   -> (SLS.UStmt, SLE.UExpr rt)
simpleFunctionBody _ n retDSF bF args = let rE = namedE n st in  (grouped (declare n (retDSF args) : bF rE args), rE)
  where
    st = sTypeFromStanType $ declType $ retDSF args

comment :: NonEmpty Text -> SLS.UStmt
comment = SLS.SComment

profile :: Text -> SLS.UStmt -> SLS.UStmt
profile = SLS.SProfile

print :: TypedList SLE.UExpr args -> SLS.UStmt
print = SLS.SPrint

reject :: TypedList SLE.UExpr args -> SLS.UStmt
reject = SLS.SReject

scoped :: SLS.UStmt -> SLS.UStmt
scoped s = SLS.SGroup SLS.Scoping
           [SLS.SContext (SLA.modifyVarCtxt SLA.enterNewScope)
           , s
           , SLS.SContext (SLA.modifyVarCtxt SLA.leaveScope)
           ]

context :: (SLA.ASTCtxt -> SLA.ASTCtxt) -> SLS.UStmt
context = SLS.SContext

grouped :: Traversable f => f SLS.UStmt -> SLS.UStmt
grouped = SLS.SGroup SLS.UnBracketed

groupedWithBrackets :: Traversable f => f SLS.UStmt -> SLS.UStmt
groupedWithBrackets = SLS.SGroup SLS.Bracketed

insertIndexBinding :: SLE.IndexKey -> SLE.LExpr EIndexArray -> SLA.ASTCtxt -> SLA.ASTCtxt
insertIndexBinding ik ie = SLA.modifyIndexCtxt $ \(SLA.IndexLookupCtxt a b) -> SLA.IndexLookupCtxt a (Map.insert ik ie b)

insertSizeBinding :: SLE.IndexKey -> SLE.LExpr EInt -> SLA.ASTCtxt -> SLA.ASTCtxt
insertSizeBinding ik ia = SLA.modifyIndexCtxt $ \(SLA.IndexLookupCtxt a b) -> SLA.IndexLookupCtxt (Map.insert ik ia a) b

insertIndexAndSize :: SLE.IndexKey ->  SLE.LExpr EIndexArray -> SLE.LExpr EInt ->  SLA.ASTCtxt -> SLA.ASTCtxt
insertIndexAndSize ik ie ia = insertIndexBinding ik ie . insertSizeBinding ik ia

lowerM :: SLE.UExpr t -> SLS.VarModifier SLE.UExpr t
lowerM = SLS.VarLower

upperM :: SLE.UExpr t -> SLS.VarModifier SLE.UExpr t
upperM = SLS.VarUpper

offsetM :: SLE.UExpr t -> SLS.VarModifier SLE.UExpr t
offsetM = SLS.VarOffset

multiplierM :: SLE.UExpr t -> SLS.VarModifier SLE.UExpr t
multiplierM = SLS.VarMultiplier

{-
declDims :: DeclSpec SLE.UExpr t -> Vec (DeclDimension t) (SLE.UExpr EInt)
declDims (ScalarSpec _ _) = VNil
declDims (VectorSpec _ l _) = l ::: VNil
declDims (MatrixSpec _ r c _) = r ::: c ::: VNil
declDims (ArraySpec _ dims ds) = dims Vec.++ declDims ds
declDims (TupleSpec _) = VNil

declVMS :: DeclSpec t -> SLS.VarModifiers SLE.UExpr (ScalarType t)
declVMS (DeclSpec _ _ vms) = vms
declVMS (ArraySpec _ _ ids) = declVMS ids
declVMS (TupleSpec _) = []
-}
