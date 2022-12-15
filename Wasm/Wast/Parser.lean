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
open Get
open Operation
open Func
open Module

def typeP : Parsec Char String Unit Type' := do
  let ps ← getParserState
  let iorf ← (string "i" <|> string "f")
  let bits ← bitSizeP
  match iorf with
  | "i" => pure $ Type'.i bits
  | "f" => pure $ Type'.f bits
  | _ => parseError $ .trivial ps.offset .none $ hints0 Char


def getP : Parsec Char String Unit (Get x) :=
  -- TODO: implement locals!!!
  pure $ Get.from_stack

def stripGet (α : Type') (x : Get α) : Get' :=
  match x with
  | .from_stack => Get'.from_stack
  | .by_name n => Get'.by_name n
  | .by_index i => Get'.by_index i

def nopP : Parsec Char String Unit Operation :=
  string "nop" *> pure .nop

def constP : Parsec Char String Unit Operation := do
  -- TODO: we'll use ps when we'll add more types into `Type'`.
  -- let _ps ← getParserState
  let x ← numUniTP
  pure $ Operation.const (numUniType x) x

 mutual

  partial def get'ViaGetP (α  : Type') : Parsec Char String Unit Get' :=
    attempt (opP >>= (pure ∘ Get'.from_operation)) <|>
    (getP >>= (pure ∘ stripGet α))

  partial def opP : Parsec Char String Unit Operation :=
    Char.between '(' ')' $ owP *>
      nopP <|> constP <|> addP

  partial def opsP : Parsec Char String Unit (List Operation) := do
    sepEndBy' opP owP

  partial def addP : Parsec Char String Unit Operation := do
    -- TODO: we'll use ps when we'll add more types into `Type'`.
    -- let _ps ← getParserState
    let add_t : Type' ←
      string "i32.add" *> (pure $ .i 32) <|>
      string "i64.add" *> (pure $ .i 64) <|>
      string "f32.add" *> (pure $ .f 32) <|>
      string "f64.add" *> (pure $ .f 64)
    ignoreP
    let (arg_1 : Get') ← get'ViaGetP add_t
    owP
    let (arg_2 : Get') ← get'ViaGetP add_t
    owP
    pure $ Operation.add add_t arg_1 arg_2
end


def exportP : Parsec Char String Unit String := do
  Char.between '(' ')' do
    discard $ string "export"
    ignoreP
    -- TODO: are escaped quotation marks legal export names?
    let export_label ← Char.between '\"' '\"' $ many' $ noneOf "\"".data
    pure $ String.mk export_label

def genLocalP (x : String) : Parsec Char String Unit Local := do
  discard $ string x
  let olabel ← (option' ∘ attempt) (ignoreP *> nameP)
  let typ ← ignoreP *> typeP
  pure $ match olabel with
  | .none => Local.mk 0 .none typ
  | .some l => Local.mk 0 (.some l) typ

def paramP : Parsec Char String Unit Local :=
  genLocalP "param"

def localP : Parsec Char String Unit Local :=
  genLocalP "local"

def manyLispP (p : Parsec Char String Unit α) : Parsec Char String Unit (List α) :=
  sepEndBy' (attempt (single '(' *> owP *> p <* owP <* single ')')) owP

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

def resultP : Parsec Char String Unit (List Type') :=
  string "result" *> ignoreP *> sepEndBy' typeP owP

-- def brResultP : Parsec Char String Unit Type' :=
--   single '(' *> owP *> resultP <* owP <* single ')'

def brResultsP : Parsec Char String Unit (List Type') :=
  List.join <$> manyLispP resultP

def funcP : Parsec Char String Unit Func := do
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


def moduleP : Parsec Char String Unit Module := do
  Char.between '(' ')' do
    owP <* (string "module")
    let oname ← option' (attempt $ ignoreP *> nameP)
    let ofuns ← option' (attempt $ ignoreP *> sepEndBy' funcP owP)
    let funs := optional ofuns []
    owP
    pure $ Module.mk oname funs


end textparser
