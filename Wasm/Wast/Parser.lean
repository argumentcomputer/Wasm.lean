import Megaparsec
import Megaparsec.Common
import Megaparsec.Errors.Bundle
import Megaparsec.Parsec

import Wasm.Wast.AST
import Wasm.Wast.BitSize
import Wasm.Wast.Name
import Wasm.Wast.Num
import Wasm.Wast.Parser.Common

open Megaparsec
open Megaparsec.Common
open Megaparsec.Errors.Bundle
open Megaparsec.Parsec
open MonadParsec

open Wasm.Wast.AST
open Wasm.Wast.Name
open Wasm.Wast.Parser.Common
open Wasm.Wast.Num.Num.Nat
open Wasm.Wast.Num.Num.Int
open Wasm.Wast.Num.Num.Float
open Wasm.Wast.Num.Uni


/- Text parser for WASM AST.
  The current intentions are to only parse S-expressions. This means
  the interpreter will (probably) throw on naked/not well-formed instructions.
-/
namespace  Wasm.Wast.Parser
section textparser

open Type'
open Local
open Global
open BlockLabel
open Operation
open Func
open Module

def bracketed (p : Parsec Char String Unit α) :=
  Seq.between (single '(' *> owP) (owP <* single ')') p

def bracketedWs (p : Parsec Char String Unit α) :=
  owP *> bracketed p <* owP

def oneOfTwoP (pa : Parsec Char String Unit α)
              (pb : Parsec Char String Unit β)
    : Parsec Char String Unit (Except α β) :=
  .error <$> pa <|> .ok <$> pb

/- Sometimes – mainly for module parsing, where declarations can be
  arbitrarily interspersed – we need a way to parse a mix of parsers.

  Additionally, and crucially, we don't want to use `attempt`, as it
  messes with error reporting.

  Consider that the "common prefix" we
  would use `attempt` for, brackets, is always known.
-/
def mixOfTwoLispP (pa : Parsec Char String Unit α)
                  (pb : Parsec Char String Unit β)
    : Parsec Char String Unit (List α × List β) := do
  let mix ← sepEndBy' (bracketed (oneOfTwoP pa pb)) owP
  let either exc acc := match exc with
    | .error a => (a :: acc.1, acc.2)
    | .ok b => (acc.1, b :: acc.2)
  pure $ mix.foldr either ([],[])

def manyLispP (p : Parsec Char String Unit α)
    : Parsec Char String Unit (List α) :=
  sepEndBy' (attempt (bracketed p)) owP

def typeP : Parsec Char String Unit Type' :=
  (single 'i' *> .i <$> bitSizeP) <|> (single 'f' *> .f <$> bitSizeP)

def localLabelP : Parsec Char String Unit LocalLabel :=
  .by_index <$> (hexP <|> decimalP) <|>
  .by_name <$> nameP

def globalLabelP : Parsec Char String Unit GlobalLabel :=
  .by_index <$> (hexP <|> decimalP) <|>
  .by_name <$> nameP

def structLabelP : Parsec Char String Unit BlockLabelId :=
  .by_index <$> (hexP <|> decimalP) <|>
  .by_name <$> nameP

def exportP : Parsec Char String Unit String := bracketed $
  string "export" *> ignoreP *>
  -- TODO: are escaped quotation marks legal export names?
  let export_label := Char.between '\"' '\"' $ many' $ noneOf "\"".data
  String.mk <$> export_label

private def anonLocalsP : Parsec Char String Unit (List Local) := do
  let ts ← sepEndBy' typeP owP
  pure $ ts.map (Local.mk .none)

private def identifiedLocalP : Parsec Char String Unit (List Local) := do
  let id ← nameP <* ignoreP
  let t ← typeP
  pure [Local.mk (.some id) t]

def brLocsP (x : String) : Parsec Char String Unit (List Local) :=
  let p := string x *> ignoreP *> (identifiedLocalP <|> anonLocalsP)
  List.join <$> manyLispP p

def genLocalP (x : String) : Parsec Char String Unit Local :=
  string x *> ignoreP *>
  Local.mk <$> option' (nameP <* ignoreP) <*> typeP

def paramP : Parsec Char String Unit Local :=
  genLocalP "param"

def localP : Parsec Char String Unit Local :=
  genLocalP "local"

def nilParamsP : Parsec Char String Unit (List Local) :=
  brLocsP "param"

def nilLocalsP : Parsec Char String Unit (List Local) :=
  brLocsP "local"

def singleResultP : Parsec Char String Unit Type' := bracketed $
  string "result" *> ignoreP *> typeP

def resultP : Parsec Char String Unit (List Type') :=
  string "result" *> ignoreP *> sepEndBy' typeP owP

def brResultsP : Parsec Char String Unit (List Type') :=
  List.join <$> manyLispP resultP

private def nopP : Parsec Char String Unit Operation :=
  string "nop" *> pure .nop

private def dropP : Parsec Char String Unit Operation :=
  string "drop" *> pure .drop

private def constP : Parsec Char String Unit Operation := do
  -- TODO: we'll use ps when we'll add more types into `Type'`.
  -- let _ps ← getParserState
  let x ← numUniTP
  pure $ Operation.const (numUniType x) x

private def localOpP : Parsec Char String Unit Operation := do
  let op ← (string "local.get" *> pure Operation.local_get)
       <|> (string "local.set" *> pure .local_set)
       <|> (string "local.tee" *> pure .local_tee)
  ignoreP *> op <$> localLabelP

private def globalOpP : Parsec Char String Unit Operation := do
  let op ← (string "global.get" *> pure Operation.global_get)
       <|> (string "global.set" *> pure .global_set)
  ignoreP *> op <$> globalLabelP

private def brOpP : Parsec Char String Unit Operation := do
  let op ← (string "br_if" *> pure Operation.br_if)
       <|> (string "br" *> pure .br)
  ignoreP *> op <$> structLabelP

 mutual

  partial def getP : Parsec Char String Unit Get' :=
    (.from_operation <$> attempt opP) <|> pure .from_stack

  partial def opP : Parsec Char String Unit Operation := bracketed $
    nopP <|> dropP <|> constP <|> selectP <|>
    iUnopP "eqz" .eqz <|>
    binopP "eq" .eq <|> binopP "ne" .ne <|>
    iBinopP "lt_u" .lt_u <|> iBinopP "lt_s" .lt_s <|>
    iBinopP "gt_u" .gt_u <|> iBinopP "gt_s" .gt_s <|>
    iBinopP "le_u" .le_u <|> iBinopP "le_s" .le_s <|>
    iBinopP "ge_u" .ge_u <|> iBinopP "ge_s" .ge_s <|>
    fBinopP "lt" .lt <|> fBinopP "gt" .gt <|>
    fBinopP "le" .le <|> fBinopP "ge" .ge <|>
    iUnopP "clz" .clz <|> iUnopP "ctz" .ctz <|> iUnopP "popcnt" .popcnt <|>
    binopP "add" .add <|> binopP "sub" .sub <|> binopP "mul" .mul <|>
    fBinopP "div" .div <|> fBinopP "max" .max <|> fBinopP "min" .min <|>
    iBinopP "div_s" .div_s <|> iBinopP "div_u" .div_u <|>
    iBinopP "rem_s" .rem_s <|> iBinopP "rem_u" .rem_u <|>
    iBinopP "and" .and <|> iBinopP "or" .or <|> iBinopP "xor" .xor <|>
    iBinopP "shl" .shl <|>
    iBinopP "shr_u" .shr_u <|> iBinopP "shr_s" .shr_s <|>
    iBinopP "rotl" .rotl <|> iBinopP "rotr" .rotr <|>
    localOpP <|> globalOpP <|>
    blockOpP <|> ifP <|> brOpP

  partial def opsP : Parsec Char String Unit (List Operation) := do
    sepEndBy' opP owP

  partial def selectP : Parsec Char String Unit Operation := do
    discard $ string "select"
    let t? ← option' (attempt (ignoreP *> singleResultP)) <* owP
    let g₁ ← getP <* owP
    let g₂ ← getP <* owP
    let g₃ ← getP <* owP
    pure $ .select t? g₁ g₂ g₃

  partial def blockOpP : Parsec Char String Unit Operation := do
  let op ← (string "block" *> pure Operation.block)
       <|> (string "loop" *> pure .loop)
    let id ← option' (attempt (ignoreP *> nameP))
    let pts ← owP *> nilParamsP
    let rts ← owP *> brResultsP
    let ops ← opsP
    pure $ op id pts rts ops

  partial def ifP : Parsec Char String Unit Operation := do
    discard $ string "if"
    let id ← option' (attempt (ignoreP *> nameP))
    let pts ← owP *> nilParamsP
    let rts ← owP *> brResultsP
    let g ← getP
    let thens ← bracketedWs $ string "then" *> owP *> opsP
    let elses ← bracketedWs $ string "else" *> owP *> opsP
    pure $ .if id pts rts g thens elses

  partial def iUnopP (opS : String) (unopMk : Type' → Get' → Operation)
              : Parsec Char String Unit Operation := do
    let type : Type' ←
      string s!"i32.{opS}" *> (pure $ .i 32) <|>
      string s!"i64.{opS}" *> (pure $ .i 64)
    owP
    let arg ← getP
    owP
    pure $ unopMk type arg

  partial def aBinopP (tChar : Char) (con : BitSize → Type') (opS : String)
                      (binopMk : Type' → Get' → Get' → Operation)
              : Parsec Char String Unit Operation := do
    -- TODO: we'll use ps when we'll add more types into `Type'`.
    -- let _ps ← getParserState
    let type ←
      string s!"{tChar}32.{opS}" *> (pure $ con 32) <|>
      string s!"{tChar}64.{opS}" *> (pure $ con 64)
    owP
    let arg_1 ← getP
    owP
    let arg_2 ← getP
    owP
    pure $ binopMk type arg_1 arg_2

  partial def iBinopP : String → (Type' → Get' → Get' → Operation)
              → Parsec Char String Unit Operation := aBinopP 'i' .i

  partial def fBinopP : String → (Type' → Get' → Get' → Operation)
              → Parsec Char String Unit Operation := aBinopP 'f' .f

  partial def binopP (opS : String) (binopMk : Type' → Get' → Get' → Operation)
              : Parsec Char String Unit Operation :=
    iBinopP opS binopMk <|> fBinopP opS binopMk

end

def globalTypeP : Parsec Char String Unit GlobalType :=
  let mutP := string "mut" *> ignoreP
  let constTP := GlobalType.mk false <$> typeP
  let varTP := bracketed $ GlobalType.mk true <$> (mutP *> typeP)
  constTP <|> varTP

/-
TODO: the initial expression for a global has to be a constant expression.
Currently, for us this means only `iₙ.const`. However, we should extend this
when we add support for:
- `ref.null`
- `ref.func x`
- imports: it also accepts `global.get i` where `i`s init is of constP form
see https://webassembly.github.io/spec/core/valid/instructions.html#constant-expressions
-/
def globalP : Parsec Char String Unit Global := do
  string "global" *> ignoreP
  let oname ← option' (nameP <* ignoreP)
  let gt ← globalTypeP <* ignoreP
  let init ← bracketed constP
  pure ⟨oname, gt, init⟩

def funcP : Parsec Char String Unit Func := do
  -- either we have a trivial case `(func)` or we must parse whitespace
  discard $ string "func"
  let oname ← option' (attempt (ignoreP *> nameP))
  let oexp ← owP *> option' (attempt exportP <* owP)
  let ops ← option' nilParamsP
  let ps := optional ops []
  let rtypes ← brResultsP
  let ols ← option' nilLocalsP
  let ls := optional ols []
  let oops ← option' opsP
  let ops := optional oops []
  pure $ Func.mk oname oexp ps rtypes ls ops

-- NB: A module consists of a sequence of fields that can occur in any order.
-- All definitions and their respective bound identifiers scope over the entire
-- module, including the text preceding them.
def moduleP : Parsec Char String Unit Module := bracketedWs do
  discard $ string "module"
  let oname ← option' (attempt (ignoreP *> nameP))
  let (globals, funs) ← owP *> mixOfTwoLispP globalP funcP

  pure $ Module.mk oname globals funs


end textparser
