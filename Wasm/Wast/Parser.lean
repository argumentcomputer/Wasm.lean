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
open Operation
open Func
open Module

def manyLispP (p : Parsec Char String Unit α) : Parsec Char String Unit (List α) :=
  sepEndBy' (attempt (single '(' *> owP *> p <* owP <* single ')')) owP

def typeP : Parsec Char String Unit Type' := do
  let ps ← getParserState
  let iorf ← (string "i" <|> string "f")
  let bits ← bitSizeP
  match iorf with
  | "i" => pure $ Type'.i bits
  | "f" => pure $ Type'.f bits
  | _ => parseError $ .trivial ps.offset .none $ hints0 Char

def localLabelP : Parsec Char String Unit LocalLabel :=
  .by_index <$> (hexP <|> decimalP) <|>
  .by_name <$> nameP

def globalLabelP : Parsec Char String Unit GlobalLabel :=
  .by_index <$> (hexP <|> decimalP) <|>
  .by_name <$> nameP

def resultP : Parsec Char String Unit (List Type') :=
  string "result" *> ignoreP *> sepEndBy' typeP owP

def brResultP : Parsec Char String Unit (List Type') :=
  single '(' *> owP *> resultP <* owP <* single ')'

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
  ignoreP
  pure $ op (←localLabelP)

private def brP : Parsec Char String Unit Operation := do
  string "br" *> ignoreP
  let idx ← hexP <|> decimalP
  pure $ .br ⟨idx⟩

private def brifP : Parsec Char String Unit Operation := do
  string "br_if" *> ignoreP
  let idx ← hexP <|> decimalP
  pure $ .br ⟨idx⟩

 mutual

  partial def getP : Parsec Char String Unit Get' :=
    attempt (pure ∘ .from_operation =<< opP) <|>
    pure .from_stack

  partial def opP : Parsec Char String Unit Operation :=
    Char.between '(' ')' $ owP *>
      nopP <|> dropP <|> constP <|>
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
      localOpP <|> blockP <|> loopP <|> ifP <|>
      brP <|> brifP
      <* owP

  partial def opsP : Parsec Char String Unit (List Operation) := do
    sepEndBy' opP owP

  partial def blockP : Parsec Char String Unit Operation := do
    string "block" *> ignoreP
    let ts ← brResultsP
    let ops ← opsP
    owP <* option' (string "end")
    pure $ .block ts ops

  partial def loopP : Parsec Char String Unit Operation := do
    string "loop" *> ignoreP
    let ts ← brResultsP
    let ops ← opsP
    owP <* option' (string "end")
    pure $ .loop ts ops

  partial def ifP : Parsec Char String Unit Operation := do
    string "if" *> ignoreP
    let ts ← brResultsP
    string "then" *> ignoreP
    let thens ← opsP
    string "else" *> ignoreP
    let elses ← opsP
    owP <* option' (string "end")
    pure $ .if ts thens elses

  partial def iUnopP (opS : String) (unopMk : Type' → Get' → Operation)
              : Parsec Char String Unit Operation := do
    let type : Type' ←
      string s!"i32.{opS}" *> (pure $ .i 32) <|>
      string s!"i64.{opS}" *> (pure $ .i 64)
    ignoreP
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
    ignoreP
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


def exportP : Parsec Char String Unit String :=
  Char.between '(' ')' $
    string "export" *> ignoreP *>
    -- TODO: are escaped quotation marks legal export names?
    let export_label := Char.between '\"' '\"' $ many' $ noneOf "\"".data
    String.mk <$> export_label

def genLocalP (x : String) : Parsec Char String Unit Local :=
  string x *> ignoreP *>
  Local.mk 0 <$> option' (nameP <* ignoreP) <*> typeP

def paramP : Parsec Char String Unit Local :=
  genLocalP "param"

def localP : Parsec Char String Unit Local :=
  genLocalP "local"

def nilParamsP : Parsec Char String Unit (List Local) := do
  manyLispP paramP

def nilLocalsP : Parsec Char String Unit (List Local) :=
  manyLispP localP

def reindexLocals (start : Nat := 0) (ps : List Local) : List Local :=
  (ps.foldl (
      fun acc x =>
        (acc.1 + 1, {x with index := acc.1} :: acc.2)
    ) (start, [])
  ).2.reverse

def globalTypeP : Parsec Char String Unit GlobalType :=
  let mutP := owP *> string "mut" *> ignoreP
  (GlobalType.mk false <$> typeP) <|>
  (Char.between '(' ')' $ GlobalType.mk true <$> (mutP *> typeP))

/-
TODO: the initial expression for a global has to be a constant expression.
Currently, for us this means only `iₙ.const`. However, we should extend this
when we add support for:
- `ref.null`
- `ref.func x`
- imports: it also accepts `global.get i` where `i`s init is of constP form
see https://webassembly.github.io/spec/core/valid/instructions.html#constant-expressions
-/
def globalP : Parsec Char String Unit Global :=
  Char.between '(' ')' do
    owP *> string "global" *> ignoreP
    let oname ← option' (nameP <* ignoreP)
    let gt ← globalTypeP
    let init ← ignoreP *>
      Char.between '(' ')' (owP *> constP <* owP)
    pure ⟨0, oname, gt, init⟩

def funcP : Parsec Char String Unit Func :=
  Char.between '(' ')' do
    owP <* (string "func")
    -- let oname ← option' (ignoreP *> nameP)
    let oname ← option' (attempt $ ignoreP *> nameP)
    let oexp ← option' (attempt $ owP *> exportP)
    let ops ← option' (attempt $ owP *> nilParamsP)
    let ps := reindexLocals 0 $ optional ops []
    let psn := ps.length
    let rtypes ← attempt $ owP *> brResultsP
    let ols ← option' (attempt $ owP *> nilLocalsP)
    let ls := reindexLocals psn $ optional ols []
    let oops ← option' (attempt $ owP *> opsP)
    let ops := optional oops []
    owP
    pure $ Func.mk oname oexp ps rtypes ls ops

-- TODO: A module consists of a sequence of fields that can occur in any order. -- All definitions and their respective bound identifiers scope over the entire
-- module, including the text preceding them.
def moduleP : Parsec Char String Unit Module :=
  Char.between '(' ')' do
    owP <* string "module"
    let oname ← option' (attempt $ ignoreP *> nameP)
    let oglobals ← option' (ignoreP *> sepEndBy' (attempt globalP) owP)
    let globals := optional oglobals []
    let ofuns ← option' (attempt $ owP *> sepEndBy' funcP owP)
    let funs := optional ofuns []
    owP
    pure $ Module.mk oname globals funs


end textparser
