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
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Stan.Language.Statements
  (
    module Stan.Language.Statements
  )
  where

import qualified Stan.Language.Statement as SLS
import qualified Stan.Language.ASTContext as SLA
import Stan.Language.Expressions
  (intE,
    namedE,
    namedSizeE,
    ExprList,
    IndexKey,
    IntE,
    LExpr,
    UExpr )
import Stan.Language.Types
    ( sTypeFromStanType,
      EIndexArray,
      EType(..),
      GenSType(..),
      SType(SInt),
      ScalarType,
      StanType(..),
      TypedList(TNil, (:>)),
      VecToSameTypedListF,
      SameTypedListToVecF,
      GenSTypeList,
      SameTypeList,
      AllGenSTypes,
      vecToSameTypedListF,
      zipTypedListsWith,
    )
import Stan.Language.Indexing
    ( Vec(..),
      DeclDimension,
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
      functionArgTypes)

import qualified Data.Vec.Lazy as Vec
import qualified Data.Type.Nat as DT
import Data.Type.Nat (Nat, SNat)
import Data.Type.Equality (type (:~:)(..), gcastWith)

import Prelude hiding (Nat)
import Relude.Extra
import qualified Data.Map.Strict as Map

type StanName = Text

type VecToTListC f n = VecToSameTypedListF f EInt n
type TListToVecC f n = SameTypedListToVecF f EInt n

--type VecToTListAC n t = VecToSameTypedListF UExpr EInt (n `DT.Plus` DeclDimension t)

data DeclSpec t where
  DeclSpec :: StanType t -> Vec (DeclDimension t) (UExpr EInt) -> [SLS.VarModifier UExpr (ScalarType t)] -> DeclSpec t
  ArraySpec :: (forall f. VecToTListC f n, forall f.TListToVecC f n, GenSTypeList (SameTypeList EInt n))
    => SNat (DT.S n) -> Vec (DT.S n) (UExpr EInt) -> DeclSpec t -> DeclSpec (EArray (DT.S n) t)
  TupleSpec :: TypedList StanType ts -> DeclSpec (ETuple ts)

data NamedDeclSpec t = NamedDeclSpec StanName (DeclSpec t)

declName :: NamedDeclSpec t -> StanName
declName (NamedDeclSpec n _) = n

decl :: NamedDeclSpec t -> DeclSpec t
decl (NamedDeclSpec _ ds) = ds

declType :: DeclSpec t -> StanType t
declType (DeclSpec st _ _) = st
declType (ArraySpec n _ ds) = StanArray n (declType ds)
declType (TupleSpec ts) = StanTuple ts

declDims :: DeclSpec t -> Vec (DeclDimension t) (UExpr EInt)
declDims (DeclSpec _ dims _) = dims
declDims (ArraySpec _ dims ds) = dims Vec.++ declDims ds
declDims (TupleSpec _) = VNil

declVMS :: DeclSpec t -> [SLS.VarModifier UExpr (ScalarType t)]
declVMS (DeclSpec _ _ vms) = vms
declVMS (ArraySpec _ _ ids) = declVMS ids
declVMS (TupleSpec _) = []

replaceDeclVMs :: [SLS.VarModifier UExpr (ScalarType t)] -> DeclSpec t -> DeclSpec t
replaceDeclVMs vms = \case
  DeclSpec st vdims _-> DeclSpec st vdims vms
  ArraySpec n arrDims ds -> ArraySpec n arrDims (replaceDeclVMs vms ds)
  TupleSpec sts -> TupleSpec sts

addVMs :: [SLS.VarModifier UExpr (ScalarType t)] -> DeclSpec t -> DeclSpec t
addVMs vms' = \case
  DeclSpec st vdims vms -> DeclSpec st vdims (vms <> vms')
  ArraySpec n arrDims ds -> ArraySpec n arrDims (addVMs vms' ds)
  TupleSpec sts -> TupleSpec sts

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

arraySpec :: (forall f.VecToTListC f n, forall f.TListToVecC f n, GenSTypeList (SameTypeList EInt n))
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

tuple2Spec :: StanType t1 -> StanType t2 -> DeclSpec (ETuple [t1, t2])
tuple2Spec st1 st2 = TupleSpec (st1 :> st2 :> TNil)

tuple3Spec :: StanType t1 -> StanType t2 -> StanType t3 -> DeclSpec (ETuple [t1, t2, t3])
tuple3Spec st1 st2 st3 = TupleSpec (st1 :> st2 :> st3 :> TNil)


-- functions for ease of use and exporting.  Monomorphised to UStmt, etc.
declare' :: Text -> StanType t -> Vec (DeclDimension t) (UExpr EInt) -> [SLS.VarModifier UExpr (ScalarType t)] -> SLS.UStmt
declare' vn vt iDecls = SLS.SDeclare vn vt (DeclIndexVecF iDecls)

declare :: Text -> DeclSpec t -> SLS.UStmt
declare vn (DeclSpec st indices vms) = declare' vn st indices vms
declare vn ds@(ArraySpec _ arrDims ids) = declare' vn (declType ds) (arrDims Vec.++ declDims ids) $ declVMS ids
declare vn (TupleSpec sts) = declare' vn (StanTuple sts) VNil []

declareN :: NamedDeclSpec t -> SLS.UStmt
declareN (NamedDeclSpec n ds) = declare n ds

declareAndAssign' :: Text -> StanType t -> Vec (DeclDimension t) (UExpr EInt) -> [SLS.VarModifier UExpr (ScalarType t)] -> UExpr t -> SLS.UStmt
declareAndAssign' vn vt iDecls vms = SLS.SDeclAssign vn vt (DeclIndexVecF iDecls) vms

declareAndAssign :: Text -> DeclSpec t -> UExpr t -> SLS.UStmt
declareAndAssign vn (DeclSpec vt indices vms) = declareAndAssign' vn vt indices vms
declareAndAssign vn ads@(ArraySpec _ arrDims ids) = declareAndAssign' vn (declType ads) (arrDims Vec.++ declDims ids) $ declVMS ids
declareAndAssign vn (TupleSpec sts) = declareAndAssign' vn (StanTuple sts) VNil []

declareAndAssignN :: NamedDeclSpec t -> UExpr t -> SLS.UStmt
declareAndAssignN (NamedDeclSpec vn ds) = declareAndAssign vn ds

addToTarget :: UExpr EReal -> SLS.UStmt
addToTarget = SLS.STarget

assign :: UExpr t -> UExpr t -> SLS.UStmt
assign = SLS.SAssign

-- doing it this way avoids using Stans += syntax.  I just expand.
-- to do otherwise I would have to add a constructor to Stmt
opAssign :: (ta ~ BinaryResultT bop ta tb) => SBinaryOp bop -> UExpr ta -> UExpr tb -> SLS.UStmt
opAssign = SLS.SOpAssign

plusEq, (+=) :: (ta ~ BinaryResultT BAdd ta tb) => UExpr ta -> UExpr tb -> SLS.UStmt
plusEq = opAssign SAdd
(+=) = opAssign SAdd

minusEq, (-=) :: (ta ~ BinaryResultT BSubtract ta tb) => UExpr ta -> UExpr tb -> SLS.UStmt
minusEq = opAssign SSubtract
(-=) = opAssign SSubtract

timesEq, (*=) :: (ta ~ BinaryResultT BMultiply ta tb) => UExpr ta -> UExpr tb -> SLS.UStmt
timesEq = opAssign SMultiply
(*=) = opAssign SMultiply

divEq, (/=) :: (ta ~ BinaryResultT BDivide ta tb) => UExpr ta -> UExpr tb -> SLS.UStmt
divEq = opAssign SDivide
(/=) = opAssign SDivide

data DensityWithArgs g where
  DensityWithArgs :: Density g args -> TypedList UExpr args -> DensityWithArgs g

withDWA :: (forall args.Density g args -> TypedList UExpr args -> r) -> DensityWithArgs g -> r
withDWA f (DensityWithArgs d args) = f d args

target :: UExpr EReal -> SLS.UStmt
target = SLS.STarget

sample :: UExpr t -> Density t args -> TypedList UExpr args -> SLS.UStmt
sample = SLS.SSample

sampleW, (|~|) :: UExpr t -> DensityWithArgs t  -> SLS.UStmt
sampleW ue (DensityWithArgs d al)= SLS.SSample ue d al
ue |~| dwa = sampleW ue dwa


--intVecToLoopVFTs :: Text -> Vec.Vec n IntE -> TypeList VarAndForType

for :: forall t . GenSType (SLS.ForEachSlice t)
    => Text -> SLS.ForType t -> (UExpr (SLS.ForEachSlice t) -> SLS.UStmt) -> SLS.UStmt
for loopCounter ft bodyF = case ft of
  SLS.SpecificNumbered se' ee' -> scoped $ SLS.SFor loopCounter se' ee' $ bodyF (namedE loopCounter SInt)
  SLS.IndexedLoop ik -> scoped $ SLS.SFor loopCounter (intE 1) (namedSizeE ik) $ bodyF (namedE loopCounter SInt)
  SLS.SpecificIn e -> scoped $ SLS.SForEach loopCounter e $ bodyF loopCounterE
--  IndexedIn _ e -> SForEach loopCounter e $ bodyF loopCounterE
  where
    loopCounterE = namedE loopCounter $ genSType @(SLS.ForEachSlice t)

loopOver :: GenSType (SLS.ForEachSlice t)
         => UExpr t -> Text -> (UExpr (SLS.ForEachSlice t) -> SLS.UStmt) -> SLS.UStmt
loopOver container loopVarName = for loopVarName (SLS.SpecificIn container)
{-# INLINEABLE loopOver #-}

ftSized :: UExpr EInt -> SLS.ForType EInt
ftSized = SLS.SpecificNumbered (intE 1)

loopSized :: UExpr EInt -> Text -> (UExpr EInt -> SLS.UStmt) -> SLS.UStmt
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

vftSized :: Text -> UExpr EInt -> SLS.VarAndForType EInt
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

ifThen :: UExpr EBool -> SLS.UStmt -> SLS.UStmt
ifThen ce sTrue = SLS.SIfElse ((ce, sTrue) :| []) nullS

ifThenElse :: NonEmpty (UExpr EBool, SLS.UStmt) -> SLS.UStmt -> SLS.UStmt
ifThenElse = SLS.SIfElse

while :: UExpr EBool -> SLS.UStmt -> SLS.UStmt
while = SLS.SWhile

break :: SLS.UStmt
break = SLS.SBreak

continue :: SLS.UStmt
continue = SLS.SContinue

function :: AllGenSTypes args => Function rt args -> TypedList (FuncArg Text) args -> (TypedList UExpr args -> (SLS.UStmt, UExpr rt)) -> SLS.UStmt
function fd argNames bodyF = scoped $ SLS.SFunction fd argNames $ grouped [bodyS, SLS.SReturn ret]
  where
    argTypes = {- typeListToTypedListOfTypes $ -} functionArgTypes fd
    argExprs = zipTypedListsWith (namedE . funcArgName) argNames argTypes
    (bodyS, ret) = bodyF argExprs

{-
densityFunction :: Traversable f => Density gt args -> TypedList (FuncArg Text) (gt ': args) -> (TypedList UExpr (gt ': args) -> (f SLS.UStmt, UExpr EReal)) -> SLS.UStmt
densityFunction fd argNames bodyF = SDensity fd argNames bodyS ret
  where
    argTypes = typeListToTypedListOfTypes $ densityFunctionArgTypes fd
    argExprs = zipTypedListsWith (namedE . funcArgName) argNames argTypes
    (bodyS, ret) = bodyF argExprs
-}

simpleFunctionBody :: Function rt pts
                   -> StanName
                   -> (ExprList pts -> DeclSpec rt)
                   -> (UExpr rt -> ExprList pts -> [SLS.UStmt])
                   -> ExprList pts
                   -> (NonEmpty SLS.UStmt, UExpr rt)
simpleFunctionBody _ n retDSF bF args = let rE = namedE n st in  (declare n (retDSF args) :| bF rE args, rE)
  where
    st = sTypeFromStanType $ declType $ retDSF args

comment :: NonEmpty Text -> SLS.UStmt
comment = SLS.SComment

profile :: Text -> SLS.UStmt -> SLS.UStmt
profile = SLS.SProfile

print :: TypedList UExpr args -> SLS.UStmt
print = SLS.SPrint

reject :: TypedList UExpr args -> SLS.UStmt
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

insertIndexBinding :: IndexKey -> LExpr EIndexArray -> SLA.ASTCtxt -> SLA.ASTCtxt
insertIndexBinding k ie (SLA.ASTCtxt vlc (SLA.IndexLookupCtxt a b)) =
  SLA.ASTCtxt vlc $ SLA.IndexLookupCtxt a (Map.insert k ie b)

insertSizeBinding :: IndexKey -> LExpr EInt -> SLA.ASTCtxt -> SLA.ASTCtxt
insertSizeBinding k ie (SLA.ASTCtxt vlc (SLA.IndexLookupCtxt a b)) =
  SLA.ASTCtxt vlc $ SLA.IndexLookupCtxt (Map.insert k ie a) b

lowerM :: UExpr t -> SLS.VarModifier UExpr t
lowerM = SLS.VarLower

upperM :: UExpr t -> SLS.VarModifier UExpr t
upperM = SLS.VarUpper

offsetM :: UExpr t -> SLS.VarModifier UExpr t
offsetM = SLS.VarOffset

multiplierM :: UExpr t -> SLS.VarModifier UExpr t
multiplierM = SLS.VarMultiplier
