{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

module Stan.Functions.Containers
  (
    module Stan.Functions.Containers
  )
  where
import qualified Stan.Functions.Constraints as SFC

import qualified Stan.Language.Types as SLT
import qualified Stan.Language.TypedList as SLTL
import Stan.Language.TypedList (TypedList(..))
import qualified Stan.Language.Functions as SLF
import qualified Stan.Language.Indexing as SLI
import qualified Stan.Language.Expressions as SLE

import qualified GHC.TypeLits as TE
import GHC.TypeLits (ErrorMessage((:<>:)))
import Data.Type.Nat (SNatI)
import Data.Type.Equality (type (~))
import Prelude hiding (Nat)

array_num_elements :: (SNatI n, SLT.GenSType t) => SLE.UExpr (SLT.EArray n t) -> SLE.IntE
array_num_elements a = SLE.functionE (SLF.simpleFunction "inv") (a :> TNil)

toVectorFunction :: forall t' t . (SFC.Vectorable t, SFC.Vector t') => Text -> SLE.UExpr t -> SLE.UExpr t'
toVectorFunction fName t = SLE.functionE (SLF.simpleFunction fName) (t :> TNil)

to_vector :: SFC.Vectorable t => SLE.UExpr t -> SLE.UExpr SLT.ECVec
to_vector = toVectorFunction "to_vector"

to_row_vector :: SFC.Vectorable t => SLE.UExpr t -> SLE.UExpr SLT.ERVec
to_row_vector = toVectorFunction "to_vector"

scalarCVec :: SLE.UExpr SLT.EReal -> SLE.UExpr SLT.ECVec
scalarCVec x = SLE.functionE (SLF.simpleFunction "") (x :> TNil)

scalarRVec :: SLE.UExpr SLT.EReal -> SLE.UExpr SLT.ERVec
scalarRVec x = SLE.functionE (SLF.simpleFunction "") (x :> TNil)

to_array_1d :: (SFC.TypeOneOf t [SLT.ECVec, SLT.ERVec], SFC.GenSType t) => SLE.UExpr t -> SLE.UExpr (SLT.EArray1 SLT.EReal)
to_array_1d v = SLE.functionE (SLF.simpleFunction "to_array_1d") (v :> TNil)

size :: (SFC.IsContainer t, SFC.GenSType t) => SLE.UExpr t -> SLE.IntE --Function EInt '[t]
size t = SLE.functionE (SLF.simpleFunction "size") (t :> TNil)
{-# INLINEABLE size #-}

fmin ::  SFC.VectorizedReal t => SLE.UExpr t -> SLE.UExpr t -> SLE.UExpr t
fmin t t' = SLE.functionE (SLF.simpleFunction "fmin") (t :> t' :> TNil)

fmax ::  SFC.VectorizedReal t => SLE.UExpr t -> SLE.UExpr t -> SLE.UExpr t
fmax t t' = SLE.functionE (SLF.simpleFunction "fmax") (t :> t' :> TNil)

containerReductionFunction :: SFC.RealContainer t =>  Text -> SLE.UExpr t ->  SLE.UExpr SLT.EReal --SLF.Function SLT.EReal '[t]
containerReductionFunction fName t = SLE.functionE (SLF.simpleFunction fName) (t :> TNil)

mean, sd, variance, min, max, sum :: SFC.RealContainer t =>  SLE.UExpr t ->  SLE.UExpr SLT.EReal --SLF.Function SLT.EReal '[t]
mean = containerReductionFunction "mean"
sd = containerReductionFunction "sd"
variance = containerReductionFunction "variance"
min = containerReductionFunction "min"
max = containerReductionFunction "max"
sum = containerReductionFunction "sum"

sumInt :: SLE.IntArrayE -> SLE.IntE --Function EInt '[EIntArray]
sumInt a = SLE.functionE (SLF.simpleFunction "sum") (a :> TNil)

rep_vector :: SLE.RealE -> SLE.IntE -> SLE.UExpr SLT.ECVec --Function ECVec '[EReal, EInt]
rep_vector x n = SLE.functionE (SLF.simpleFunction "rep_vector") (x :> n :> TNil)

rep_row_vector :: SLE.RealE -> SLE.IntE -> SLE.UExpr SLT.ERVec --Function ECVec '[EReal, EInt]
rep_row_vector x n = SLE.functionE (SLF.simpleFunction "rep_row_vector") (x :> n :> TNil)

ones_vector :: SLE.IntE -> SLE.UExpr SLT.ECVec
ones_vector n = SLE.functionE (SLF.simpleFunction "ones_vector") (n :> TNil)

ones_row_vector :: SLE.IntE -> SLE.UExpr SLT.ERVec
ones_row_vector n = SLE.functionE (SLF.simpleFunction "ones_row_vector") (n :> TNil)

{-
type family NInts (n :: Nat) :: [EType] where
  NInts Z = '[]
  NInts (S n) = EInt ': NInts n

rep_array :: (GenSType t, GenTypeList (NInts n), SNatI n) => Function (EArray n t) (t ': NInts n)
rep_array = simpleFunction "rep_array"
{-# INLINEABLE rep_array #-}


-}
-- this pleases me
rep_array' :: (SFC.GenSType t, SLTL.GenTypeList (SLTL.SameTypeList SLT.EInt n), SNatI n) => SLF.Function (SLT.EArray n t) (t ': SLTL.SameTypeList SLT.EInt n)
rep_array' = SLF.simpleFunction "rep_array"

rep_array1 :: SFC.GenSType t => SLE.UExpr t -> SLE.IntE -> SLE.UExpr (SLT.EArray (SLT.S SLT.Z) t)
rep_array1 x n = SLE.functionE rep_array' (x :> n :> TNil)

rep_array2 ::  SFC.GenSType t => SLE.UExpr t -> SLE.IntE -> SLE.IntE -> SLE.UExpr (SLT.EArray (SLT.S (SLT.S SLT.Z)) t)
rep_array2 x n m = SLE.functionE rep_array' (x :> n :> m :> TNil)

rep_array3 ::  SFC.GenSType t => SLE.UExpr t -> SLE.IntE -> SLE.IntE -> SLE.IntE -> SLE.UExpr (SLT.EArray (SLT.S (SLT.S (SLT.S SLT.Z))) t)
rep_array3 x n m l = SLE.functionE rep_array' (x :> n :> m :> l :> TNil)


dot_product :: (SFC.TypeOneOf t '[SLT.ECVec, SLT.ERVec], SFC.GenSType t, SFC.TypeOneOf t' '[SLT.ECVec, SLT.ERVec], SFC.GenSType t')
            => SLE.UExpr t -> SLE.UExpr t' -> SLE.RealE --Function EReal '[t, t']
dot_product t t' = SLE.functionE (SLF.simpleFunction "dot_product") (t :> t' :> TNil)

{-
type family RepArgs (t :: SLT.EType) :: [SLT.EType] where
  RepArgs SLT.ECVec = [SLT.EReal, SLT.EInt]
  RepArgs SLT.ERVec = [SLT.EReal, SLT.EInt]
  RepArgs SLT.EMat = [SLT.EReal, SLT.EInt, SLT.EInt]
--  RepArgs ESqMat = [SLT.EReal, SLT.EInt]
  RepArgs t = SLE.TypeError (SLE.Text "Cannot fill " :<>: SLE.ShowType t :<>: SLE.Text " like a container (e.g., vector, matrix)")

-- this might not be so useful because GHC/Haskell cannot neccessarily see through the constraints
rep_container' :: (SFC.TypeOneOf t '[SLT.ECVec, SLT.EMat]) => SLT.SType t -> SLF.Function t (RepArgs t)
rep_container' st = case st of
  SLT.SCVec -> rep_vector
  SLT.SMat -> rep_matrix
--  SSqMat -> rep_sq_matrix
-}
rep_matrix ::  SLE.RealE -> SLE.IntE -> SLE.IntE -> SLE.UExpr SLT.EMat --Function EMat '[EReal, EInt, EInt]
rep_matrix x r c = SLE.functionE (SLF.simpleFunction "rep_matrix") (x :> r :> c :> TNil)

repV_matrix :: (SFC.TypeOneOf t '[SLT.ECVec, SLT.ERVec], SFC.GenSType t) => SLE.UExpr t -> SLE.IntE -> SLE.UExpr SLT.EMat -- Function EMat '[t, EInt]
repV_matrix v n = SLE.functionE (SLF.simpleFunction "rep_matrix") (v :> n :> TNil)

{-
rep_sq_matrix :: Function ESqMat '[EReal, EInt]
rep_sq_matrix = Function "rep_matrix" SSqMat (SReal ::> SInt ::> TypeNil) f
  where
    f :: TypedList u '[EReal, EInt] -> TypedList u '[EReal, EInt, EInt]
    f (a :> b :> TNil) = a :> b :> b :> TNil
{-# INLINEABLE rep_sq_matrix #-}
-}

vecArrayToMatrix :: (SFC.TypeOneOf t [SLT.ECVec, SLT.ERVec], SFC.GenSType t) => SLE.UExpr (SLT.EArray1 t) -> SLE.MatrixE --Function EMat '[EArray1 t]
vecArrayToMatrix a = SLE.functionE (SLF.simpleFunction "to_matrix") (a :> TNil)

vecToMatrix :: (SFC.TypeOneOf t [SLT.ECVec, SLT.ERVec], SFC.GenSType t) => SLE.UExpr t -> SLE.IntE -> SLE.IntE -> SLE.MatrixE -- Function EMat '[t, EInt, EInt]
vecToMatrix v r c = SLE.functionE (SLF.simpleFunction "to_matrix") (v :> r :> c :> TNil)

quad_form_diag :: (SFC.Matrix t, SFC.TypeOneOf t' [SLT.ECVec, SLT.ERVec], SFC.GenSType t')
             => SLE.UExpr t -> SLE.UExpr t' -> SLE.UExpr t --Function t '[t, t']
quad_form_diag m v = SLE.functionE (SLF.simpleFunction "quad_form_diag") (m :> v :> TNil)

segment :: (SFC.IsContainer t, SFC.GenSType t) => SLE.UExpr t -> SLE.IntE -> SLE.IntE -> SLE.UExpr t -- Function t [t, EInt, EInt]
segment c n m = SLE.functionE (SLF.simpleFunction "segment") (c :> n :> m :> TNil)

inverse :: (SFC.TypeOneOf t [SLT.EMat, SLT.ESqMat], SFC.GenSType t) => SLE.UExpr t -> SLE.UExpr t --Function t '[t]
inverse m = SLE.functionE (SLF.simpleFunction "inverse") (m :> TNil)

qr_thin_Q, qr_thin_R :: SLE.MatrixE -> SLE.MatrixE --Function EMat '[EMat]
qr_thin_Q m = SLE.functionE (SLF.simpleFunction "qr_thin_Q") (m :> TNil)
qr_thin_R m = SLE.functionE (SLF.simpleFunction "qr_thin_R") (m :> TNil)

block :: SLE.MatrixE -> SLE.IntE -> SLE.IntE -> SLE.IntE -> SLE.IntE -> SLE.MatrixE --Function EMat [EMat, EInt, EInt, EInt, EInt]
block m startRow startCol rows cols = SLE.functionE (SLF.simpleFunction "block") (m :> startRow :> startCol :> rows :> cols :> TNil)

sub_col :: SLE.MatrixE -> SLE.IntE -> SLE.IntE -> SLE.IntE -> SLE.UExpr SLT.ECVec --Function ECVec [EMat, EInt, EInt, EInt]
sub_col m startRow col rows = SLE.functionE (SLF.simpleFunction "sub_col") (m :> startRow :> col :> rows :> TNil)

sub_row :: SLE.MatrixE -> SLE.IntE -> SLE.IntE -> SLE.IntE -> SLE.UExpr SLT.ERVec --Function ERVec [EMat, EInt, EInt, EInt]
sub_row m row startCol cols = SLE.functionE (SLF.simpleFunction "sub_row") (m :> row :> startCol :> cols :> TNil)

append_col :: SLE.MatrixE -> SLE.VectorE -> SLE.MatrixE --Function EMat [EMat, ECVec]
append_col m v = SLE.functionE (SLF.simpleFunction "append_col") (m :> v :> TNil)

append_row :: SLE.MatrixE -> SLE.RVectorE -> SLE.MatrixE --Function EMat [EMat, ERVec]
append_row m r = SLE.functionE (SLF.simpleFunction "append_row") (m :> r :> TNil)

append_to_row_vector :: SLE.RVectorE -> SLE.RealE -> SLE.RVectorE --Function ERVec [ERVec, EReal]
append_to_row_vector rv x = SLE.functionE (SLF.simpleFunction "append_col") (rv :> x :> TNil)

append_to_vector :: SLE.VectorE -> SLE.RealE -> SLE.VectorE --Function ECVec [ECVec, EReal]
append_to_vector v x = SLE.functionE (SLF.simpleFunction "append_row") (v :> x :> TNil)

rows, cols :: SFC.Matrix t => SLE.UExpr t -> SLE.IntE --Function EInt '[t]
rows m = SLE.functionE (SLF.simpleFunction "rows") (m :> TNil)
cols m = SLE.functionE (SLF.simpleFunction "cols") (m :> TNil)


diagonal :: SFC.Matrix t => SLE.UExpr t -> SLE.VectorE --Function ECVec '[t]
diagonal m = SLE.functionE (SLF.simpleFunction "diagonal") (m :> TNil)

-- NB: Stan docs warn against using this because there's usually a more efficient option
-- But I'm not sure what to do with multiple draws from uncorrelated normals
diag_matrix :: SFC.Vector t => SLE.UExpr t -> SLE.UExpr SLT.ESqMat --Function ESqMat '[t]
diag_matrix v = SLE.functionE (SLF.simpleFunction "diag_matrix") (v :> TNil)

diag_pre_multiply :: (SFC.Vector t, SFC.Matrix t') => SLE.UExpr t -> SLE.UExpr t' -> SLE.UExpr t' -- Function t' [t, t']
diag_pre_multiply v m = SLE.functionE (SLF.simpleFunction "diag_pre_multiply") (v :> m :> TNil)

diag_post_multiply :: (SFC.Vector vt, SFC.Matrix mt) => SLE.UExpr mt -> SLE.UExpr vt -> SLE.UExpr mt --Function t' [t, t']
diag_post_multiply m v = SLE.functionE (SLF.simpleFunction "diag_post_multiply") (m :> v :> TNil)

{-
diag_pre_multiply :: SFC.Matrix t => SLE.UExpr SLT.ERVec -> SLE.UExpr t -> SLE.UExpr t --Function t '[ERVec, t]
diag_pre_multiply rv m = SLE.functionE (SLF.simpleFunction "diag_pre_multiply") (rv :> m :> TNil)

diag_post_multiply :: SFC.Matrix t => SLE.UExpr t -> SLE.UExpr SLT.ECVec -> SLE.UExpr t --Function t '[t, ECVec]
diag_post_multiply m cv = SLE.functionE (SLF.simpleFunction "diag_post_multiply") (m :> cv :> TNil)
-}
