import Wasm
import Wasm.Engine
import Wasm.Wast.AST
import Wasm.Wast.Expr
import Wasm.Wast.Name
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
open Wasm.Wast.Expr
open Wasm.Wast.Name
open Wasm.Wast.Num
open Wasm.Wast.Parser
open Wasm.Leb128

open Num.Digit
open Num.Nat
open Num.Int
open Num.Float
open Wasm.Wast.Num.Uni

open Megaparsec.Parsec

def sameName (_n₁ : Option $ Name x) (_n₂ : Option $ Name x) : Option (Name "kek") := mkName "kek"
#eval sameName (mkName "lol") (mkName "lol")
-- #eval sameName (mkName "lol") (mkName "kek")

def main : IO Unit := do

  IO.println "* * *"
  IO.println "f32 is represented as:"
  void $ parseTestP typeP "f32"
  IO.println "* * *"

  IO.println "* * *"
  IO.println "i32.const -1 is represented as:"
  void $ parseTestP iP "i32.const -1"
  IO.println "* * *"

  IO.println "* * *"
  IO.println "i32.add (i32.const 42) is represented as:"
  void $ parseTestP addP "i32.add (i32.const 42)"
  IO.println "* * *"

  IO.println "* * *"
  let i := "(func)"
  IO.println s!"{i} is represented as:"
  void $ parseTestP funcP i
  IO.println "* * *"

  IO.println "* * *"
  let i := "param $t i32"
  IO.println s!"{i} is represented as:"
  void $ parseTestP paramP i
  IO.println "* * *"

  IO.println "* * *"
  let i := "(param $t i32) (param $coocoo f32)"
  IO.println s!"{i} is represented as:"
  void $ parseTestP nilParamsP i
  IO.println "* * *"

  IO.println "* * *"
  let i := "(param i32) (param $coocoo f32)  ( param i64 ) ( something_else )"
  IO.println s!"{i} is represented as:"
  void $ parseTestP nilParamsP i
  IO.println "* * *"

  IO.println "* * *"
  let i := "( result i32)"
  IO.println s!"{i} is represented as:"
  void $ parseTestP brResultsP i
  IO.println "* * *"

  -- IO.println "* * *"
  -- let i := "(func (param $x i32) (param $y i32) (result i32)
  --   (i32.add (local.get $y) (local.get $x))
  -- )"
  -- IO.println s!"{i} is represented as:"
  -- void $ parseTestP funcP i
  -- IO.println "* * *"

  IO.println "* * *"
  let i := "(func (param $x i32) (param $y i32) (result i32)
  )"
  IO.println s!"{i} is represented as:"
  void $ parseTestP funcP i
  IO.println "* * *"

  IO.println "* * *"
  let i := "(func (param $x i32) (param i32) (result i32))"
  -- unnamed param should have id 1
  IO.println s!"{i} is represented as:"
  void $ parseTestP funcP i
  IO.println "* * *"

  IO.println "* * *"
  let i := "(block (result i32) (i32.const 1) end)"
  IO.println s!"{i} is represented as:"
  void $ parseTestP opP i
  IO.println "* * *"

  IO.println "* * *"
  let i := "if (result i32) then (i32.const 42) else (i32.const 9)"
  IO.println s!"{i} is represented as:"
  void $ parseTestP ifP i
  IO.println "* * *"

  IO.println "* * *"
  let i := "(func (param $x i32) (param i32) (result i32) (i32.add (i32.const 40) (i32.const 2)))"
  -- unnamed param should have id 1
  IO.println s!"{i} is represented as:"
  void $ parseTestP funcP i
  /-
  (Func.mk
    none
    none
    [ (Local.name (LocalName.mk x (Type'.i (32 : BitSize))))
    , (Local.index (LocalIndex.mk 1 (Type'.i (32 : BitSize)))) ]
    (some (Type'.i (32 : BitSize)))
    []
    [
      (Operation.add
        (Add'.i32
          (Get.const (Sum.inl (ConstInt (32 : BitSize) 40)) : Get (Type'.i (32 : BitSize)))
          (Get.const (Sum.inl (ConstInt (32 : BitSize)  2)) : Get (Type'.i (32 : BitSize)))
        )
    ]
  )
  -/
  IO.println "* * *"

  IO.println "* * *"

  let i := "(module
        (func (export \"main\")
            (result i32)

            (i32.add
                (i32.const 1499550000)
                (i32.add (i32.const 9000) (i32.const 17))
            )
        )
    )"

  -- unnamed param should have id 1
  IO.println s!"{i} is represented as:"
  let o_parsed_module ← parseTestP moduleP i
  match o_parsed_module.2 with
  | .error _ => IO.println "FAIL"
  | .ok parsed_module => do
    IO.println s!">>> !!! >>> It is converted to bytes as: {mtob parsed_module}"
    let f := System.mkFilePath ["/tmp", "special.wasm"]
    let h ← IO.FS.Handle.mk f IO.FS.Mode.write
    h.write $ mtob parsed_module
    IO.println "It's recorded to disk at /tmp/special.wasm"


  let i := s!"(module
        (func (export \"two_ints\")
            (result i32) (result i32)
            (i32.add
                (i32.const 1499550000)
                (i32.add (i32.const 9000) (i32.const 17))
            )
            (i32.add (i32.const -1) (i32.const 1))
        )
    )"

  -- unnamed param should have id 1
  IO.println s!"{i} is represented as:"
  let o_parsed_module ← parseTestP moduleP i
  match o_parsed_module.2 with
  | .error _ => IO.println "FAIL"
  | .ok parsed_module => do
    IO.println s!">>> !!! >>> It is converted to bytes as: {mtob parsed_module}"
    let f := System.mkFilePath ["/tmp", "mtob.59.wasm"]
    let h ← IO.FS.Handle.mk f IO.FS.Mode.write
    h.write $ mtob parsed_module
    IO.println "It's recorded to disk at /tmp/mtob.59.wasm"

  let i := "(module
        (func (param $x_one i32) (param $three i32) (param $y_one i32) (result i32) (i32.add (i32.const 40) (i32.const 2)))
        (func (param $x_two f32) (param f32) (param f32) (result i32) (i32.add (i32.const 12) (i32.const 30)))
  )"

  -- unnamed param should have id 1
  IO.println s!"{i} is represented as:"
  let o_parsed_module ← parseTestP moduleP i
  match o_parsed_module.2 with
  | .error _ => IO.println "FAIL"
  | .ok parsed_module => do
    IO.println s!">>> !!! >>> It is converted to bytes as: {mtob parsed_module}"
    let f := System.mkFilePath ["/tmp", "mtob.91.wasm"]
    let h ← IO.FS.Handle.mk f IO.FS.Mode.write
    h.write $ mtob parsed_module
    IO.println "It's recorded to disk at /tmp/mtob.91.wasm"


  let i := "(module
    (func (param $x i32) (param i32) (result i32) (i32.add (i32.const 40) (i32.const 2)))
  )"

  -- unnamed param should have id 1
  IO.println s!"{i} is represented as:"
  let o_parsed_module ← parseTestP moduleP i
  match o_parsed_module.2 with
  | .error _ => IO.println "FAIL"
  | .ok parsed_module => do
    IO.println s!">>> !!! >>> It is converted to bytes as: {mtob parsed_module}"
    let f := System.mkFilePath ["/tmp", "mtob.47.wasm"]
    let h ← IO.FS.Handle.mk f IO.FS.Mode.write
    h.write $ mtob parsed_module
    IO.println "It's recorded to disk at /tmp/mtob.47.wasm"

  -- NAKED CONST IS NOT IMPLEMENTED YET: https://zulip.yatima.io/#narrow/stream/20-meta/topic/WAST.20pair.20prog/near/32237
  -- let i := "(module
  --   (func (param $x i32) (param i32) (result i32) (i32.const 42))
  -- )"
  -- -- unnamed param should have id 1
  -- IO.println s!"{i} is represented as:"
  -- let o_parsed_module ← parseTestP moduleP i
  -- match o_parsed_module.2 with
  -- | .error _ => IO.println "FAIL"
  -- | .ok parsed_module => do
  --   IO.println s!">>> !!! >>> It is converted to bytes as: {mtob parsed_module}"
  --   IO.println "It's recorded to disk at /tmp/mtob.44.wasm"
  --   let f := System.mkFilePath ["/tmp", "mtob.44.wasm"]
  --   let h ← IO.FS.Handle.mk f IO.FS.Mode.write
  --   h.write $ mtob parsed_module

  let i := "(module
    ( func (param $x i32) (param i32) )
  )"
  -- unnamed param should have id 1
  IO.println s!"{i} is represented as:"
  let o_parsed_module ← parseTestP moduleP i
  match o_parsed_module.2 with
  | .error _ => IO.println "FAIL"
  | .ok parsed_module => do
    IO.println s!">>> !!! >>> It is converted to bytes as: {mtob parsed_module}"
    let f := System.mkFilePath ["/tmp", "mtob.41.wasm"]
    let h ← IO.FS.Handle.mk f IO.FS.Mode.write
    h.write $ mtob parsed_module
    IO.println "It's recorded to disk at /tmp/mtob.41.wasm"

  let i := "(module
    (func (param $x i32))
  )"
  -- unnamed param should have id 1
  IO.println s!"{i} is represented as:"
  let o_parsed_module ← parseTestP moduleP i
  match o_parsed_module.2 with
  | .error _ => IO.println "FAIL"
  | .ok parsed_module => do
    IO.println s!">>> !!! >>> It is converted to bytes as: {mtob parsed_module}"
    let f := System.mkFilePath ["/tmp", "mtob.40.wasm"]
    let h ← IO.FS.Handle.mk f IO.FS.Mode.write
    h.write $ mtob parsed_module
    IO.println "It's recorded to disk at /tmp/mtob.40.wasm"

  let i := "(module
    ( func )
  )"
  -- unnamed param should have id 1
  IO.println s!"{i} is represented as:"
  let o_parsed_module ← parseTestP moduleP i
  match o_parsed_module.2 with
  | .error _ => IO.println "FAIL"
  | .ok parsed_module => do
    IO.println s!">>> !!! >>> It is converted to bytes as: {mtob parsed_module}"
    let f := System.mkFilePath ["/tmp", "mtob.24.wasm"]
    let h ← IO.FS.Handle.mk f IO.FS.Mode.write
    h.write $ mtob parsed_module
    IO.println "It's recorded to disk at /tmp/mtob.24.wasm"

  IO.println "* * *"

  -- TODO: pack more ascii into the easter egg with i64
  let i := "(module
    (func $main (export \"main\")
      (param $x i32)
      (param i32)
      (result i32 i32)

      (block (result i32) (i32.const 3) (i32.add (br 0) (i32.const 9)))
      (i32.add
        (i32.const 1499550000)
        (i32.add (i32.const 9000) (i32.const 17))
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
    let store := mkStore m
    let ofid := fidByName store "main"
    let uni_num_zero := NumUniT.i $ ConstInt.mk 32 0
    let se_zero := StackEntry.StackEntry.num uni_num_zero
    IO.println $ match ofid with
    | .none => s!"THERE IS NO FUNCTION CALLED `main`"
    | .some fid =>
      let eres := run store fid $ Stack.mk [se_zero, se_zero]
      match eres with
      | .ok stack2 => match stack2.es with
        | [] => "UNEXPECTED RESULT"
        | xs => s!"!!!!!!!!!!!!!! SUCCESS !!!!!!!!!!!!!!!!\n{xs}"
      | .error ee => s!"FAILED TO RUN `main` CORRECTLY: {ee}"

  let mut x := 0
  x := 1
  IO.println s!"Thanks for using Webassembly with Lean, you're #{x}!"
  let x1 := 1499559017
  IO.println s!"BE who you want to be: {x1.toByteArrayBE}..."
  IO.println s!"LEarn lean for fun and profit: {x1.toByteArrayLE}!"

  pure ()
