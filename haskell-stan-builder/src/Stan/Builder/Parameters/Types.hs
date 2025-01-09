{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}

module Stan.Builder.Parameters.Types
  (
    ParameterTag
  , taggedParameterName
  , taggedParameterType
  , parameterExpr
  , parameterTagExpr
  , FunctionToDeclare(..)
  , TData(..)
  , Parameter(..)
  , given
  , build
  , mapped
  , Parameters
  , tagsAsExprs
  , tagsAsParams
  , parametersAsExprs
  , DeclCode(..)
  , TransformedParameterLocation(..)
  , BuildParameter(..)
  , BParameterCollection(..)
  , bParameterName
  , bParameterSType
  , bParameterStanType
  , addBuildParameterE
  , withBPDeps
  , lookupParameterExpressions
  , lookupTDataExpressions
  , addBuiltExpressionToMap
  )
  where

import Prelude hiding (All)

import qualified Stan.Language.Types as SLT
import Stan.Language.Statement (UStmt)
import qualified Stan.Language.Statement as SLS
import qualified Stan.Language.Statements as SLS
import qualified Stan.Language.CodeWriter as SLC
import Stan.Language.Recursion (hfmap, htraverse)
import qualified Data.GADT.Compare as GC
import qualified Data.GADT.Show as GC
import qualified Data.Type.Equality as GC
import qualified Data.Dependent.Map as DM

import Data.Type.Equality (TestEquality(testEquality))
import qualified Text.Show
import qualified Data.Set as Set
import Stan.Language.Expression (UExpr)
import Stan.Language.Expressions (ExprList, namedE)
import Stan.Language.Types (sTypeToEType)

  -- ultimately, we should not expose this constructor.  So to get one of these you have to add a Builder to the DMap.
data ParameterTag :: SLT.EType -> Type where
  ParameterTag :: SLT.SType t -> SLT.VarName -> ParameterTag t

taggedParameterType :: ParameterTag t -> SLT.SType t
taggedParameterType (ParameterTag st _) = st

taggedParameterName :: ParameterTag t -> SLT.VarName
taggedParameterName (ParameterTag _ n ) = n

instance GC.GEq ParameterTag where
  geq a b  = GC.testEquality (taggedParameterType a) (taggedParameterType b)

instance GC.GCompare ParameterTag where
  gcompare a b = case GC.geq a b of
    Just GC.Refl -> case compare (taggedParameterName a) (taggedParameterName b) of
      EQ -> GC.GEQ
      LT -> GC.GLT
      GT -> GC.GGT
    -- The below is "incomplete" if missing the "EQ" case. But that won't compile since a and b are not provably the same
    -- Or uses undefined and warns about that
    Nothing -> case compare (sTypeToEType $ taggedParameterType a) (sTypeToEType $ taggedParameterType b) of
      LT -> GC.GLT
      GT -> GC.GGT
      EQ -> undefined --GC.GEQ

instance Show (ParameterTag t) where
  show (ParameterTag st n) = "<" <> show st <> ": " <> show n <> ">"

instance GC.GShow ParameterTag where gshowsPrec = Text.Show.showsPrec

parameterTagFromBP :: BuildParameter t -> ParameterTag t
parameterTagFromBP p = ParameterTag (bParameterSType p) (bParameterName p)

parameterTagExpr :: ParameterTag t -> UExpr t
parameterTagExpr (ParameterTag st n) = namedE n st

--data UseParameter :: TE.EType -> Type where
--  AsIs :: ParameterTag t -> UseParameter t
--  Mapped :: (UExpr t -> UExpr t') -> UseParameter t -> UseParameter t'



--useParameterExpr :: UseParameter t -> UExpr t
--useParameterExpr (AsIs pt) = parameterTagExpr pt
--useParameterExpr (Mapped g pt) = g $ useParameterExpr pt

--mapParameter :: (UExpr t -> UExpr t') -> UseParameter t -> UseParameter t'
--mapParameter = Mapped

-- Transformed Data declarations can only depend on other transformed data, so we need
-- a wrapper type to enforce that.

--type Givens ts = TE.TypedList UExpr ts

-- parameterized by the type of the parameter
-- Each can include statements to be added to
-- transformed data block
data Parameter :: SLT.EType -> Type where
  GivenP :: UExpr t -> Parameter t
  BuildP :: ParameterTag t -> Parameter t
  MappedP :: (UExpr t -> UExpr t') -> Parameter t -> Parameter t'

parameterExpr :: Parameter t -> UExpr t
parameterExpr (GivenP e) = e
parameterExpr (BuildP p) = parameterTagExpr p
parameterExpr (MappedP g p) = g $ parameterExpr p

given :: UExpr t -> Parameter t
given = GivenP

build :: ParameterTag t -> Parameter t
build = BuildP

mapped :: (UExpr t -> UExpr t') -> Parameter t -> Parameter t'
mapped = MappedP

type Parameters ts = SLT.TypedList Parameter ts
type ParameterTags ts = SLT.TypedList ParameterTag ts

tagsAsExprs :: ParameterTags ts -> ExprList ts
tagsAsExprs = hfmap parameterTagExpr
{-# INLINEABLE tagsAsExprs #-}

tagsAsParams :: ParameterTags ts -> Parameters ts
tagsAsParams = hfmap build
{-# INLINEABLE tagsAsParams #-}


parametersAsExprs :: Parameters ts -> ExprList ts
parametersAsExprs = hfmap parameterExpr
{-# INLINEABLE parametersAsExprs #-}

data FunctionToDeclare = FunctionToDeclare Text UStmt

data DeclCode t where
  DeclRHS :: UExpr t -> DeclCode t
  DeclCodeF :: (UExpr t -> SLC.CodeWriter ()) -> DeclCode t

data TData :: SLT.EType -> Type where
  TData :: SLS.NamedDeclSpec t
        -> [FunctionToDeclare]
        -> SLT.TypedList TData ts
        -> (ExprList ts -> DeclCode t) -- code for the transformed data block
        -> TData t

parameterTagFromTData :: TData t -> ParameterTag t
parameterTagFromTData (TData (SLS.NamedDeclSpec n (SLS.ScalarSpec st _)) _ _ _) = ParameterTag (SLT.sTypeFromStanType st) n
parameterTagFromTData (TData (SLS.NamedDeclSpec n (SLS.VectorSpec st _ _)) _ _ _) = ParameterTag (SLT.sTypeFromStanType st) n
parameterTagFromTData (TData (SLS.NamedDeclSpec n (SLS.MatrixSpec st _ _ _)) _ _ _) = ParameterTag (SLT.sTypeFromStanType st) n
parameterTagFromTData (TData (SLS.NamedDeclSpec n (SLS.ArraySpec sn _ ds)) _ _ _) = ParameterTag (SLT.sTypeFromStanType $ SLT.StanArray sn $ SLS.declType ds) n
parameterTagFromTData (TData (SLS.NamedDeclSpec n (SLS.TupleSpec ts)) _ _ _) = ParameterTag (SLT.sTypeFromStanType $ SLT.StanTuple $ hfmap SLS.declType ts) n
--parameterTagFromTData (TData (SLS.NamedDeclSpec n (SLS.TupleSpec ts)) _ _ _) = ParameterTag (SLT.sTypeFromStanType $ SLT.StanTuple ts) n

-- should we also check names?
instance TestEquality TData where
  testEquality tda tdb = testEquality (f tda) (f tdb) where
    f (TData (SLS.NamedDeclSpec _ (SLS.ScalarSpec st _)) _ _ _) = SLT.sTypeFromStanType st
    f (TData (SLS.NamedDeclSpec _ (SLS.VectorSpec st _ _)) _ _ _) = SLT.sTypeFromStanType st
    f (TData (SLS.NamedDeclSpec _ (SLS.MatrixSpec st _ _ _)) _ _ _) = SLT.sTypeFromStanType st
    f (TData (SLS.NamedDeclSpec _ (SLS.ArraySpec sn _ ds)) _ _ _) = SLT.sTypeFromStanType $ SLT.StanArray sn $ SLS.declType ds
    f (TData (SLS.NamedDeclSpec _ (SLS.TupleSpec ts)) _ _ _) = SLT.sTypeFromStanType $ SLT.StanTuple $ hfmap SLS.declType ts

--withTData :: TData t -> (forall ts.TE.NamedDeclSpec t -> TE.TypedList TData ts -> (TE.ExprList ts -> UExpr t) -> r) -> r
--withTData (TData nds tds eF) f = f nds tds eF

--tDataNamedDecl :: TData t -> TE.NamedDeclSpec t
--tDataNamedDecl (TData nds _ _ _) = nds

data TransformedParameterLocation  where
  TransformedParametersBlock :: TransformedParameterLocation
  ModelBlock :: TransformedParameterLocation
  ModelBlockLocal :: TransformedParameterLocation

data BuildParameter :: SLT.EType -> Type where
  TransformedDataP :: TData t -> BuildParameter t
  UntransformedP :: SLS.NamedDeclSpec t
                 -> [FunctionToDeclare]
                 -> Parameters qs
                 -> (ExprList qs -> UExpr t -> SLC.CodeWriter ()) -- prior in model block
                 -> BuildParameter t
  TransformedP :: SLS.NamedDeclSpec t
               -> [FunctionToDeclare]
               -> Parameters qs -- parameters for transformation
               -> TransformedParameterLocation
               -> (ExprList qs -> DeclCode t) -- code for transformation
               -> Parameters rs -- parameters for prior (if nec)
               -> (ExprList rs -> UExpr t -> SLC.CodeWriter ()) -- prior in model block (if nec)
               -> BuildParameter t

instance TestEquality BuildParameter where
  testEquality bpa bpb = testEquality (f bpa) (f bpb) where
    f = SLT.sTypeFromStanType . SLS.declType . SLS.decl . getNamedDecl

-- Parameter Dependencies types are scoped to stay within a `Parameter t`
-- so to do anything which uses them, we need to use CPS
withBPDeps :: Monoid r => BuildParameter t -> (forall ts. Parameters ts -> r) -> r
withBPDeps (TransformedDataP (TData _ _ tds _)) f = f $ hfmap (BuildP . parameterTagFromTData) tds
withBPDeps (UntransformedP _ _ ps _) f = f ps
withBPDeps (TransformedP _ _ pq _ _ pr _) f = f pq <> f pr
--withBPDeps (ModelP _ _ pq _ ) f = f pq

data BParameterCollection = BParameterCollection { pdm :: DM.DMap ParameterTag BuildParameter, usedNames :: Set SLT.VarName }

--type BuildParameters ts = TE.TypedList BuildParameter ts

getNamedDecl :: BuildParameter t -> SLS.NamedDeclSpec t --SB.StanBuilderM md gq (TE.NamedDeclSpec t)
getNamedDecl = \case
  TransformedDataP (TData nds _ _ _) -> nds
  UntransformedP x _ _ _ -> x
  TransformedP x _ _ _ _ _ _ -> x
--  ModelP x _ _ _ -> x
--  TransformedDiffTypeP x _ _ _ _ _ _ -> x

{-
setNamedDecl :: TE.NamedDeclSpec t -> BuildParameter t -> BuildParameter t --SB.StanBuilderM md gq (Parameter t)
setNamedDecl x = \case
  TransformedDataP (TData _ y z a) -> TransformedDataP (TData x y z a)
  UntransformedP _ y z a -> UntransformedP x y z a
  TransformedP _ y z a b c  -> TransformedP x y z a b c
  ModelP _ y z a  -> ModelP x y z a
-}
--  TransformedDiffTypeP _ y z a b c d -> TransformedDiffTypeP x y z a b c d

bParameterName :: BuildParameter t -> SLT.VarName
bParameterName = SLS.declName . getNamedDecl

bParameterStanType :: BuildParameter t -> SLT.StanType t
bParameterStanType = SLS.declType . SLS.decl . getNamedDecl

bParameterSType :: BuildParameter t -> SLT.SType t
bParameterSType = SLT.sTypeFromStanType . bParameterStanType

addBuildParameterE :: BuildParameter t -> BParameterCollection -> Either Text (BParameterCollection, ParameterTag t)
addBuildParameterE bp bpc = do
  let pName =  bParameterName bp
--      pSType = bParameterSType bp
  if Set.member pName (usedNames bpc)
    then Left $ "Attempt to add " <> pName <> " to parameter collection but a parameter of that name is already present."
    else Right $ let ttn = parameterTagFromBP bp in (BParameterCollection (DM.insert ttn bp $ pdm bpc) (Set.insert pName $ usedNames bpc), ttn)

lookupParameterExpressions :: Parameters ts -> DM.DMap ParameterTag UExpr -> Either Text (SLT.TypedList UExpr ts)
lookupParameterExpressions ps eMap = htraverse f ps where
  f :: Parameter t -> Either Text (UExpr t)
  f p = case p of
      GivenP e -> return e
      BuildP ttn -> do
        case DM.lookup ttn eMap of
          Just e -> Right e
          Nothing -> Left $ taggedParameterName ttn <> " not found in expression map.  Dependency ordering issue??"
      MappedP g p' -> g <$> f p'

lookupTDataExpressions :: SLT.TypedList TData ts -> DM.DMap ParameterTag UExpr -> Either Text (SLT.TypedList UExpr ts)
lookupTDataExpressions tds = lookupParameterExpressions (hfmap (BuildP . parameterTagFromTData) tds)

addBuiltExpressionToMap :: BuildParameter t -> UExpr t -> DM.DMap ParameterTag UExpr -> DM.DMap ParameterTag UExpr
addBuiltExpressionToMap bp  =  DM.insert (parameterTagFromBP bp)
