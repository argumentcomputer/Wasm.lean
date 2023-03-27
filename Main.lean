import Wasm
import Wasm.Engine
import Wasm.Wast.Code
import Wasm.Wast.Expr
import Wasm.Wast.Name
import Wasm.Wast.Num
import Wasm.Bytes
import Wasm.Leb128

import Megaparsec.Parsec

open Wasm.Bytes
open Wasm.Engine
open Wasm.Wast.Code
open Wasm.Wast.Code.Func
open Wasm.Wast.Code.Module
open Wasm.Wast.Code.Operation
open Wasm.Wast.Expr
open Wasm.Wast.Name
open Wasm.Wast.Num
open Wasm.Leb128

open Num.Digit
open Num.Nat
open Num.Int
open Wasm.Wast.Num.Uni

open Megaparsec.Parsec

-- def sameName (_n₁ : Option $ Name x) (_n₂ : Option $ Name x) : Option (Name "kek") := mkName "kek"
-- #eval sameName (mkName "lol") (mkName "lol")
-- #eval sameName (mkName "lol") (mkName "kek")

def main : IO Unit := do

  let i := "(module
    (func $main (export \"main\")
      (param $x i32)
      (param i32)
      (result i32)

      (i32.add
        (i32.const 1819606001)
        (i32.add (i32.const 30000) (i32.const 330))
      )

    )
  )"
  -- unnamed param should have id 1
  IO.println s!"Module {i} parses to:"
  let o_parsed_module ← parseTestP moduleP i
  match o_parsed_module.2 with
  | .error _ => IO.println s!"Error: There was an error parsing the module"
  | .ok m => do
    let store := mkStore m
    let ofid := fidByName store "main"
    let uni_num_zero := NumUniT.i $ ConstInt.mk 32 0
    let se_zero := StackEntry.num uni_num_zero
    IO.println $ match ofid with
    | .none => s!"There is no function named `main`"
    | .some fid =>
      let eres := run store fid $ Stack.mk [se_zero, se_zero]
      match eres with
      | .ok stack2 => match stack2.es with
        | x :: _ => match x with
          | .num universal_number => match universal_number with
            | .i i => s!"And successfully evaluates to: {i}"
        | _ => "Error: Unexpected stack"
      | .error ee => s!"Error: Failed to run `main` with {ee}"

  pure ()
