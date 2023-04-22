import Wasm
import Wasm.Engine
import Wasm.Demo.Steps
import Wasm.Wast.AST
import Wasm.Wast.Identifier
import Wasm.Wast.Num
import Wasm.Wast.Parser
import Wasm.Bytes
import Wasm.Leb128

import Megaparsec.Parsec

open Wasm.Bytes
open Wasm.Engine
open Wasm.Wast.AST.Func
open Wasm.Wast.AST.Module
open Wasm.Wast.AST.Operation
open Wasm.Wast.Identifier
open Wasm.Wast.Num
open Wasm.Wast.Parser
open Wasm.Leb128

open Num.Digit
open Num.Nat
open Num.Int
-- open Num.Float
open Wasm.Wast.Num.Uni

open Megaparsec.Parsec

def sameIdentifier (_n₁ : Option $ Identifier x) (_n₂ : Option $ Identifier x)
                   : Option (Identifier "kek") := mkIdentifier "kek"
#eval sameIdentifier (mkIdentifier "lol") (mkIdentifier "lol")
-- #eval sameIdentifier (mkIdentifier "lol") (mkIdentifier "kek")

def yatima : Int := Id.run $ do
  let i := "(module $something_special
    (global $a i32 (i32.const 1499550000))
    (global i32 (i32.const 17))

    (func $main (export \"main\")
      (param $x i32)
      (param i32)
      (result i32 i32)

      (block (result i32) (i32.const 3) (i32.add (br 0) (i32.const 9)))
      (i32.add
        (global.get $a)
        (i32.add (i32.const 9000) (global.get 1))
      )

    )
  )"
  let o_parsed_module ← parseP moduleP "" i
  match o_parsed_module with
  | .error _ => pure $ -1
  | .ok parsed_module => pure $ run_wasm parsed_module


def main : IO Unit := do

  let i := "(module $something_special
    (global $a i32 (i32.const 1499550000))
    (global i32 (i32.const 17))

    (func $main (export \"main\")
      (param $x i32)
      (param i32)
      (result i32 i32)

      (block (result i32) (i32.const 3) (i32.add (br 0) (i32.const 9)))
      (i32.add
        (global.get $a)
        (i32.add (i32.const 9000) (global.get 1))
      )

    )
  )"
  -- unnamed param should have id 1
  IO.println s!"{i} is represented as:"
  let o_parsed_module ← parseTestP moduleP i
  let something_special_module := o_parsed_module -- We'll run it with Engine in a bit
  match o_parsed_module.2 with
  | .error _ => IO.println "FAIL"
  | .ok parsed_module => do
    IO.println s!">>> !!! >>> It is converted to bytes as: {mtob parsed_module}"
    let f := System.mkFilePath ["/tmp", "something.special.wasm"]
    let h ← IO.FS.Handle.mk f IO.FS.Mode.write
    h.write $ mtob parsed_module
    IO.println "It's recorded to disk at /tmp/something.special.wasm"

  match something_special_module.2 with
  | .error _ => IO.println s!"THERE IS A BUG IN RUNTIME TEST"
  | .ok m => do
    IO.println s!"!!!!!!!!!!!! DEMO OF WASM LEAN RUNTIME WOW !!!!!!!!!!!!!"
    IO.println s!"RUNNING FUNCTION `main` FROM A MODULE WITH REPRESENTATION:\n{m}"
    match mkStore m with
    | .error ee => IO.println s!"FAILED TO CONSTRUCT A STORE: {ee}"
    | .ok store =>
      let ofid := exportedFidByName store "main"
      let uni_num_zero := NumUniT.i $ ConstInt.mk 32 0
      let se_zero := StackEntry.StackEntry.num uni_num_zero
      IO.println $ match ofid with
      | .none => s!"THERE IS NO FUNCTION CALLED `main`"
      | .some fid =>
      ------------- RUNNING HERE --------------
        let eres := run store fid $ Stack.mk [se_zero, se_zero]
        match eres with
        | .ok (_, stack2) => match stack2.es with
          | [] => "UNEXPECTED RESULT"
          ---------------- FINALLY GET STACK ENTRIES HERE ----------------
          | xs => s!"!!!!!!!!!!!!!! SUCCESS !!!!!!!!!!!!!!!!\n{xs}"
        | .error ee => s!"FAILED TO RUN `main` CORRECTLY: {ee}"

  let mut x := 0
  x := 1
  IO.println s!"Thanks for using Webassembly with Lean, you're #{x}!"
  let x1 := 1499559017
  IO.println s!"BE who you want to be: {x1.toByteArrayBE}..."
  IO.println s!"LEarn lean for fun and profit: {x1.toByteArrayLE}!"

  pure ()
