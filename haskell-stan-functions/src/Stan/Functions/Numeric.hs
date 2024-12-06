{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

module Stan.Functions.Numeric
  (
    module Stan.Functions.Numeric
  )
  where

import qualified Stan.Functions.Constraints as SFC
import qualified Stan.Language.Types as SLT
import Stan.Language.TypedList (TypedList(..))
import qualified Stan.Language.Functions as SLF
import qualified Stan.Language.Expressions as SLE

vectorizedRealFunction :: SFC.VectorizedReal t => Text -> SLE.UExpr t -> SLE.UExpr t
vectorizedRealFunction fName t = SLE.functionE (SLF.simpleFunction fName) (t :> TNil)

logit, inv_logit, sqrt, inv_sqrt, lgamma, log, exp, log1m, atanh, lChoose, inv, abs :: SFC.VectorizedReal t => SLE.UExpr t -> SLE.UExpr t
logit = vectorizedRealFunction "logit"
inv_logit = vectorizedRealFunction "inv_logit"
sqrt = vectorizedRealFunction "sqrt"
inv_sqrt = vectorizedRealFunction "inv_sqrt"
lgamma = vectorizedRealFunction "lgamma"
log = vectorizedRealFunction "log"
exp = vectorizedRealFunction "exp"
log1m = vectorizedRealFunction "log1m"
atanh = vectorizedRealFunction "atanh"
inv = vectorizedRealFunction "inv"
abs = vectorizedRealFunction "abs"
-- vectorized log of real-valued binomial coefficient
-- see: https://mc-stan.org/docs/functions-reference/betafun.html
lChoose = vectorizedRealFunction "lChoose"

softmax, log_softmax :: SFC.VectorizedReal t => SLE.UExpr t -> SLE.UExpr t
softmax = vectorizedRealFunction "softmax"
log_softmax = vectorizedRealFunction "log_softmax"


targetVal :: SLE.UExpr SLT.EReal --SLF.Function SLT.EReal '[]
targetVal = SLE.functionE (SLF.simpleFunction "target") TNil
