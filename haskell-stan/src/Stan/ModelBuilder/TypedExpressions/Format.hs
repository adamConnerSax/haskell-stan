{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# LANGUAGE TypeApplications #-}

module Stan.ModelBuilder.TypedExpressions.Format
  (
    module Stan.ModelBuilder.TypedExpressions.Format
  )
  where

import Stan.ModelBuilder.TypedExpressions.Recursion
import Stan.ModelBuilder.TypedExpressions.Types
import Stan.ModelBuilder.TypedExpressions.TypedList
import Stan.ModelBuilder.TypedExpressions.Indexing
import Stan.ModelBuilder.TypedExpressions.Operations
import Stan.ModelBuilder.TypedExpressions.Functions
import Stan.ModelBuilder.TypedExpressions.Expressions
import Stan.ModelBuilder.TypedExpressions.Statements

import qualified Data.Functor.Foldable as RS
import qualified Data.Foldable as Foldable

import qualified Data.IntMap.Strict as IM
import qualified Data.List as List
import qualified Data.List.NonEmpty as NE
import qualified Data.Vec.Lazy as DT
import qualified Data.Type.Nat as DT
import Data.Type.Equality (type (~))
import qualified Data.Text as T

import Prelude hiding (Nat)
import qualified Data.Map.Strict as Map

import qualified Prettyprinter as PP
import Prettyprinter ((<+>))
import qualified Prettyprinter.Render.Text as PP


type CodePP = PP.Doc ()

-- we replace LExprs within statements with prettyprinted code
-- then fold up the statements to produce code
stmtToCodeE :: LStmt -> Either Text CodePP
stmtToCodeE = RS.hylo stmtToCodeAlg (hfmap exprToCode . RS.project)

lineLayout :: PP.Doc a -> PP.Doc a
lineLayout = PP.group . PP.nest 2

preferOpBreak :: CodePP -> CodePP -> CodePP -> CodePP
preferOpBreak prefix op rhs = PP.flatAlt
                              (prefix <> PP.line <> op <+> rhs)
                              (prefix <+> op <+> rhs)

stmtToCodeAlg :: StmtF (K CodePP) (Either Text CodePP) -> Either Text CodePP
stmtToCodeAlg = \case
  SDeclareF txt st divf vms -> Right $ lineLayout
                               $ stanDeclHead st (unK <$> DT.toList (unDeclIndexVecF divf)) vms <> PP.softline
                               <> PP.pretty txt <> PP.semi
  SDeclAssignF txt st divf vms rhs -> Right $ lineLayout
                                      $ preferOpBreak
                                      (stanDeclHead st (unK <$> DT.toList (unDeclIndexVecF divf)) vms <+> PP.pretty txt)
                                      PP.equals
                                      (unK rhs <> PP.semi)
  SAssignF lhs rhs -> Right $ lineLayout $ preferOpBreak (unK lhs) PP.equals (unK rhs <> PP.semi)
  SOpAssignF op lhs rhs -> Right $ lineLayout $ preferOpBreak (unK lhs) (opDoc op <> PP.equals) (unK rhs <> PP.semi)
  STargetF rhs -> Right $ lineLayout $ preferOpBreak "target" "+=" $ unK rhs <> PP.semi
  SSampleF lhs (Density dn _ _ rF) al -> Right $ lineLayout
                                         $ preferOpBreak
                                         (unK lhs)
                                         "~"
                                         (PP.pretty dn <> PP.parens (csArgList $ rF al) <> PP.semi)
  SForF txt fe te body -> (\b -> "for" <+> PP.parens (PP.pretty txt <+> "in" <+> unK fe <> PP.colon <> unK te) <+> bracketBlock b) <$> sequenceA body
  SForEachF txt e body -> (\b -> "foreach" <+> PP.parens (PP.pretty txt <+> "in" <+> unK e) <+> bracketBlock b) <$> sequence body
  SIfElseF condAndIfTrueL allFalse -> ifElseCode condAndIfTrueL allFalse
  SWhileF if' body -> (\b -> "while" <+> PP.parens (unK if') <+> bracketBlock b) <$> sequence body
  SBreakF -> Right $ "break" <> PP.semi
  SContinueF -> Right $ "continue" <> PP.semi
  SFunctionF (Function fname rt ats rF) al body re ->
    (\b -> PP.pretty (sTypeName rt) <+> PP.pretty fname <> functionArgs (applyTypedListFunctionToTypeList rF ats) (rF al)
           <+> bracketBlock (b `appendAsList` ["return" <+> unK re <> PP.semi])) <$> sequence body
  SFunctionF (IdentityFunction _) _ _ _ -> Left "Attempt to *declare* Identity function!"
  SCommentF cs -> case toList cs of
    [] -> Right mempty
    [c] -> Right $ "//" <+> PP.pretty c
    csList -> Right $ "{*" <> PP.line <> PP.indent 2 (PP.vsep $ PP.pretty <$> csList) <> PP.line <> "*}"
  SProfileF t body -> (\b -> "profile" <> PP.parens (PP.dquotes $ PP.pretty t) <+> bracketBlock b) <$> sequenceA body
  SPrintF al -> Right $ "print" <+> PP.parens (csArgList al) <> PP.semi
  SRejectF al -> Right $ "reject" <+> PP.parens (csArgList al) <> PP.semi
  SScopedF body -> bracketBlock <$> sequence body
  SBlockF bl body -> maybe (Right mempty) (fmap (\x -> PP.pretty (stmtBlockHeader bl) <+> bracketBlock x) . sequenceA) $ nonEmpty $ toList body
  SContextF mf body -> case mf of
    Just _ -> Left "stmtToCodeAlg: Impossible! SContext with a change function remaining!"
    Nothing -> blockCode <$> sequence body

indexCodeL :: [CodePP] -> CodePP
indexCodeL [] = ""
indexCodeL x = PP.brackets $ PP.hsep $ PP.punctuate "," x

{-
snatPlus1 :: DT.SNat n -> DT.SNat (DT.Plus n DT.Nat1)
snatPlus1 sn = case sn of
  DT.SZ -> DT.snat @DT.Nat1
  DT.SS ->

snatSum :: DT.SNat n1 -> DT.SNat n2 -> DT.SNat (DT.Plus n1 n2)
snatSum sn1 x = case sn1 of
  DT.SZ -> x
  DT.SS -> snatSum DT.snat x
-}

--snatSum :: DT.SNat n1 -> DT.SNat n2 -> DT.Nat


--sta1 -> NatSum

stanDeclHead :: forall t . StanType t -> [CodePP] -> [VarModifier (K CodePP) (ScalarType t)] -> CodePP
stanDeclHead st il vms = case st of
  StanArray sn arrayType -> arrayDeclHead (fromIntegral $ DT.snatToNatural sn) arrayType
--  _ -> PP.pretty (stanTypeName st)  <> indexCodeL il <> varModifiersToCode vms
  _ -> PP.pretty (stanTypeName st) <> varModifiersToCode vms <> indexCodeL il
  where
    vmToCode = \case
      VarLower x -> "lower" <> PP.equals <> unK x
      VarUpper x -> "upper" <> PP.equals <> unK x
      VarOffset x -> "offset" <> PP.equals <> unK x
      VarMultiplier x -> "multiplier" <> PP.equals <> unK x
    varModifiersToCode varModifierList =
      if null varModifierList
      then mempty
      else PP.langle <> (PP.hsep $ PP.punctuate  (PP.comma <> PP.space) $ fmap vmToCode varModifierList) <> PP.rangle
    arrayDeclHead :: (ScalarType t ~ ScalarType t') => Int -> StanType t' -> CodePP
    arrayDeclHead ad declArrayType = case declArrayType of
      StanArray innerDeclArrayDim innerDeclArrayType -> arrayDeclHead (ad + (fromIntegral $ DT.snatToNatural innerDeclArrayDim)) innerDeclArrayType
      _ -> let (adl, sdl) = List.splitAt ad il
           in "array" <> indexCodeL adl <+> stanDeclHead declArrayType sdl vms

-- add brackets and indent the lines of code
bracketBlock :: Traversable f => f CodePP -> CodePP
bracketBlock s = if length s == 1
                 then PP.group . bracketCode $ blockCode s
                 else bracketCode $ blockCode s

-- surround with brackets and indent
bracketCode :: CodePP -> CodePP
bracketCode c = PP.flatAlt
                (PP.lbrace <> PP.hardline <> PP.indent 2 c <> PP.hardline <> PP.rbrace <> PP.space) -- otherwise
                (PP.lbrace <+> c <+> PP.rbrace <> PP.space) -- if grouped and fits on one line

addSemi :: CodePP -> CodePP
addSemi c = c <> PP.semi

-- put each item of code on a separate line
blockCode :: Traversable f => f CodePP -> CodePP
blockCode ne = PP.vsep $ toList ne

-- put each line *after the first* on a new line
blockCode' :: Traversable f => f CodePP -> CodePP
blockCode' cs = case toList cs of
  [] -> mempty
  (c : csTail) -> c <> PP.vsep csTail

appendAsList :: Traversable f => f a -> [a] -> [a]
appendAsList fa as = toList fa ++ as

functionArgs:: TypeList args -> TypedList (FuncArg Text) args -> CodePP
functionArgs argTypes argNames = PP.parens $ formatFunctionArgs argCodeList
  where
    handleFA :: CodePP -> FuncArg Text t -> CodePP
    handleFA c = \case
      Arg a -> c <+> PP.pretty a
      DataArg a -> "data" <+> c <+> PP.pretty a

    arrayIndices :: SNat n -> CodePP
    arrayIndices sn = if n == 0 then mempty else PP.brackets (mconcat $ List.replicate (n-1) PP.comma)
      where n = fromIntegral $ DT.snatToNatural sn

    handleType :: SType t -> CodePP
    handleType st = case st of
      SArray sn arrayType -> "array" <> arrayIndices sn <+> handleType arrayType
      _ -> PP.pretty $ sTypeName st

    f :: SType t -> FuncArg Text t -> K CodePP t
    f st fa = K $ handleFA (handleType st) fa

    argCodeList = typedKToList $ zipTypedListsWith f (typeListToSTypeList argTypes) argNames

-- This might be wrong after switch from NE to
ifElseCode :: NonEmpty (K CodePP EBool, Either Text CodePP) -> Either Text CodePP -> Either Text CodePP
ifElseCode condAndCodeNE c = do
  let appendToNE :: NonEmpty a -> [a] -> NonEmpty a
      appendToNE (a :| as) as' = a :| as ++ as'
      (conds, ifTrueCodeEs) = NE.unzip condAndCodeNE
      condCode (e :| es) = "if" <+> PP.parens (unK e) <> PP.space :| fmap (\le -> "else if" <+> PP.parens (unK le) <> PP.space) es
      condCodeNE = condCode conds `appendToNE` ["else"]
  ifTrueCodes <- sequenceA (ifTrueCodeEs `appendToNE` [c])
  let codeNE = NE.zipWith (<+>) condCodeNE (fmap (PP.group . bracketBlock . pure @[]) ifTrueCodes)
  return $ blockCode' codeNE

data OpType = RangeOp | BOp BinaryOp

data  IExprCode :: Type where
  Bare :: CodePP -> IExprCode
  Oped ::  OpType -> CodePP -> IExprCode -- has a binary operator in it so might need parentheses
  Indexed :: CodePP -> [Int] -> IM.IntMap IExprCode -> IExprCode -- needs indexing. Carries *already sliced* indices and index expressions

data IExprCodeF :: Type -> Type where
  BareF :: CodePP -> IExprCodeF a
  OpedF :: OpType -> CodePP -> IExprCodeF a
  IndexedF :: CodePP -> [Int] -> IM.IntMap a -> IExprCodeF a

instance Functor IExprCodeF where
  fmap f = \case
    BareF doc -> BareF doc
    OpedF op c -> OpedF op c
    IndexedF c si im -> IndexedF c si (f <$> im)

instance Foldable IExprCodeF where
  foldMap f = \case
    BareF _doc -> mempty
    OpedF _ _ -> mempty
    IndexedF _ _ im -> foldMap f im

instance Traversable IExprCodeF where
  traverse g = \case
    BareF doc -> pure $ BareF doc
    OpedF op c -> pure $ OpedF op c
    IndexedF c si im -> IndexedF c si <$> traverse g im

type instance RS.Base IExprCode = IExprCodeF

instance RS.Recursive IExprCode where
  project = \case
    Bare doc -> BareF doc
    Oped op c -> OpedF op c
    Indexed iec si im -> IndexedF iec si im

instance RS.Corecursive IExprCode where
  embed = \case
    BareF doc -> Bare doc
    OpedF op c -> Oped op c
    IndexedF doc si im -> Indexed doc si im

iExprToDocAlg :: IExprCodeF CodePP -> CodePP
iExprToDocAlg = \case
  BareF doc -> doc
  OpedF _ c -> c
  IndexedF doc _ im -> doc <> PP.brackets (mconcat $ PP.punctuate ", " $ withLeadingEmpty im)

withLeadingEmpty :: IntMap CodePP -> [CodePP]
withLeadingEmpty im = imWLE where
  minIndex = Foldable.minimum $ IM.keys im
  imWLE = List.replicate minIndex mempty ++ IM.elems im

iExprToCode :: IExprCode -> CodePP
iExprToCode = RS.cata iExprToDocAlg

formatFunctionArgs :: [CodePP] -> CodePP
formatFunctionArgs cs = PP.align . PP.group
                        $ PP.flatAlt
                        (PP.encloseSep mempty mempty PP.comma cs)
                        (PP.encloseSep mempty mempty (PP.comma <> PP.space) cs)

formatDensityArgs :: [CodePP] -> CodePP
formatDensityArgs cs = PP.align . PP.group
                        $ PP.flatAlt
                        (encloseSep' mempty mempty PP.pipe PP.comma cs)
                        (encloseSep' mempty mempty (PP.pipe <> PP.space) (PP.comma <> PP.space) cs)


encloseSep' :: CodePP -> CodePP -> CodePP -> CodePP -> [CodePP] -> CodePP
encloseSep' l r s1' s ds = case ds of
  [] -> l <> r
  [d] -> l <> d <> r
  _ -> PP.cat (zipWith (<>) (l : s1' : repeat s) ds) <> r

csArgList :: TypedList (K CodePP) args -> CodePP
csArgList = formatFunctionArgs . typedKToList

prefixSurroundPrefer :: CodePP -> CodePP -> CodePP -> CodePP -> CodePP -> CodePP
prefixSurroundPrefer ifUnsplit ifSplit ls rs c = PP.group $ PP.flatAlt ifSplit ifUnsplit <> ls <> PP.align c <> rs

-- I am not sure about/do not understand the quantified constraint here.
exprToDocAlg :: IAlg LExprF (K IExprCode) -- LExprF ~> K IExprCode
exprToDocAlg = K . \case
  LNamed txt _st -> Bare $ PP.pretty txt
  LInt n -> Bare $ PP.pretty n
  LReal x -> Bare $ PP.pretty x
  LComplex x y -> Bare $ PP.parens $ PP.pretty x <+> "+" <+> "i" <> PP.pretty y -- (x + iy))
  LString t -> Bare $ PP.dquotes $ PP.pretty t
  LVector xs -> Bare $ PP.brackets $ PP.pretty $ T.intercalate ", " (show <$> xs)
  LMatrix ms -> Bare $ unNestedToCode PP.brackets [length ms] $ PP.pretty <$> concatMap DT.toList ms--PP.brackets $ PP.pretty $ T.intercalate "," $ fmap (T.intercalate "," . fmap show . DT.toList) ms
  LArray nv -> Bare $ nestedVecToCode nv
  LIntRange leM ueM -> Oped RangeOp $ maybe mempty (unK . f) leM <> PP.colon <> maybe mempty (unK . f) ueM
  LFunction (Function fn _ _ rF) al -> Bare $ PP.pretty fn <> PP.parens (csArgList $ hfmap f $ rF al)
  LFunction (IdentityFunction _) (arg :> TNil) -> Bare $ unK $ f arg
  LDensity (Density dn _ _ rF) k al -> Bare $ PP.pretty dn <> PP.parens (formatDensityArgs (unK (f k) : typedKToList (hfmap f $ rF al)))
  LBinaryOp sbo le re -> binaryOp sbo le re --Oped (binaryOpFromSBinaryOp sbo) $ unK (f $ parenthesizeOped le) <> PP.softline <> opDoc sbo <+> unK (f $ parenthesizeOped re)
  LUnaryOp op e -> Bare $ unaryOpDoc (unK (f $ parenthesizeOped e)) op
  LCond ce te fe -> Bare $ PP.group $ PP.nest 1 $ unK (f ce) <> PP.softline <> "?" <+> unK (f te) <> PP.softline <> PP.colon <+> unK (f fe)
  LSlice sn ie e -> sliced sn ie e
  LIndex sn ie e -> indexed sn ie e
  where
    f :: K IExprCode ~> K CodePP
    f = K . iExprToCode . unK
    parensIfNec :: OpType -> OpType -> CodePP -> CodePP
    parensIfNec opTApply opTIn c = case opTIn of
      RangeOp -> PP.parens c
      BOp opIn -> case opTApply of
        RangeOp -> PP.parens c
        BOp opApply -> if needParens opApply opIn then PP.parens c else c
    binaryOp :: SBinaryOp bop -> K IExprCode a -> K IExprCode b -> IExprCode -- (BinaryResultT bop a b)
    binaryOp sop le re =
      let bop = binaryOpFromSBinaryOp sop
      in Oped (BOp bop) $ case (unK le, unK re) of
        (Oped opTl l, Oped opTr r) -> parensIfNec (BOp bop) opTl l <> PP.softline <> opDoc sop <+> parensIfNec (BOp bop) opTr r
        (Oped opTl l, x) -> parensIfNec (BOp bop) opTl l <> PP.softline <> opDoc sop <+> iExprToCode x
        (x, Oped opTr r) -> iExprToCode x <> PP.softline <> opDoc sop <+> parensIfNec (BOp bop) opTr r
        (x, y) -> iExprToCode x <> PP.softline <> opDoc sop <+> iExprToCode y
    parenthesizeOped :: K IExprCode ~> K IExprCode
    parenthesizeOped x = case unK x of
       Oped bop doc -> K $ Oped bop $ PP.parens doc
       y -> K y
    addSlice :: SNat n -> K IExprCode EInt -> K IExprCode d -> [Int] -> IM.IntMap IExprCode -> ([Int], IM.IntMap IExprCode)
    addSlice sn kei _ si im = (si', im')
      where
        newIndex :: Int = fromIntegral $ DT.snatToNatural sn
        origIndex = let g n = if n `elem` si then g (n + 1) else n in g newIndex -- find the correct index in the original
        si' = origIndex : si
        im' = IM.alter (Just . maybe (unK kei) (sliced s0 kei . K)) origIndex im
    sliced :: SNat n -> K IExprCode EInt -> K IExprCode t -> IExprCode
    sliced sn kei ke = case unK ke of
      Bare c -> let (si, im) = addSlice sn kei ke [] IM.empty in Indexed c si im
      Oped _ c -> let (si, im) = addSlice sn kei ke [] IM.empty in Indexed (PP.parens c) si im
      Indexed c si im -> let (si', im') = addSlice sn kei ke si im in Indexed c si' im'
    addIndex :: SNat n -> K IExprCode (EArray (S Z) EInt) -> K IExprCode d -> [Int] -> IM.IntMap IExprCode -> IM.IntMap IExprCode
    addIndex sn kre _ke si im = im'
      where
        newIndex :: Int = fromIntegral $ DT.snatToNatural sn
        origIndex = let g n = if n `elem` si then g (n + 1) else n in g newIndex
        im' = IM.alter (Just . maybe (unK kre) (indexed s0 kre . K)) origIndex im
    indexed :: SNat n -> K IExprCode (EArray (S Z) EInt) -> K IExprCode t -> IExprCode
    indexed sn kei ke = case unK ke of
      Bare c -> Indexed c [] $ addIndex sn kei ke [] IM.empty
      Oped _ c -> Indexed (PP.parens c) [] $ addIndex sn kei ke [] IM.empty
      Indexed c si im -> Indexed c si $ addIndex sn kei ke si im

exprToIExprCode :: LExpr ~> K IExprCode
exprToIExprCode = iCata exprToDocAlg

exprToCode :: LExpr ~> K CodePP
exprToCode = K . iExprToCode . unK . exprToIExprCode

unaryOpDoc :: CodePP -> SUnaryOp op -> CodePP
unaryOpDoc ed = \case
  SNegate -> "-" <> ed
  STranspose -> ed <> "'"

boolOpDoc :: SBoolOp op -> CodePP
boolOpDoc = \case
  SEq -> PP.equals <> PP.equals
  SNEq -> "!="
  SLT -> PP.langle
  SLEq -> "<="
  SGT -> PP.rangle
  SGEq -> ">="
  SAnd -> "&&"
  SOr -> "||"

opDoc :: SBinaryOp op -> CodePP
opDoc = \case
  SAdd ->  "+"
  SSubtract -> "-"
  SMultiply -> "*"
  SDivide -> PP.slash
  SPow -> "^"
  SModulo -> "%"
  SElementWise sbo -> PP.dot <> opDoc sbo
--  SAndEqual sbo -> opDoc sbo <> PP.equals
  SBoolean bop -> boolOpDoc bop

nestedVecToCode :: NestedVec n (K IExprCode t) -> CodePP
nestedVecToCode nv = unNestedToCode PP.braces (drop 1 $ reverse dims) itemsCode
  where
    f = iExprToCode . unK
    (dims, items) = unNest nv
    itemsCode = f <$> items

-- given a way to surround a group,
-- a set of dimensions to group in order of grouping (so reverse order of left to right indexes)
-- items of code in one long list
-- produce a code item with them grouped
-- e.g., renderAsText $ unNestedCode PP.parens [2, 3] ["a","b","c","d","e","f"] = "((a, b), (c, d), (e, f))"
unNestedToCode :: (CodePP -> CodePP) -> [Int] -> [CodePP] -> CodePP
unNestedToCode surroundF dims items = surround $ go dims items
  where
--    rdims = reverse dims
    surround = surroundF . PP.hsep . PP.punctuate ", "
    group' :: Int -> [CodePP] -> [CodePP] -> [CodePP]
    group' _ [] bs = bs
    group' n as bs = let (g , as') = List.splitAt n as in group' n as' (bs ++ [surround g]) -- this is quadratic. Fix.
    go :: [Int] -> [CodePP] -> [CodePP]
    go [] as = as
    go (x : xs) as = go xs (group' x as [])

stmtBlockHeader :: StmtBlock -> Text
stmtBlockHeader = \case
  FunctionsStmts -> "functions"
  DataStmts -> "data"
  TDataStmts -> "transformed data"
  ParametersStmts -> "parameters"
  TParametersStmts -> "transformed parameters"
  ModelStmts -> "model"
  GeneratedQuantitiesStmts -> "generated quantities"

exprToText' :: PP.LayoutOptions -> LExpr t -> Text
exprToText' lo = PP.renderStrict . PP.layoutSmart lo . unK . exprToCode

exprToText :: LExpr t -> Text
exprToText = exprToText' PP.defaultLayoutOptions

printLookupCtxt :: IndexLookupCtxt -> Text
printLookupCtxt (IndexLookupCtxt s i) = "sizes: " <> T.intercalate ", " (printF <$> Map.toList s)
                                        <> "indexes: " <> T.intercalate ", " (printF <$> Map.toList i)
  where
    printF :: forall t.(Text, LExpr t) -> Text
    printF (ik, le) = "(" <> ik <> ", " <> exprToText le  <> ")"
