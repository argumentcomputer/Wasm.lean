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

  IO.println "(11) WASM demo coming soon."

  IO.println s!"Digits parse rather efficiently! And now, ergonomically!"
  let d11 : Digit 'b' := {}
  IO.println s!"{(d11 : Nat)} == 11" -- We can 'Coe'rce!

  IO.println s!"We have numbers!"
  let n222 : Option $ Nat' "22_2_2" := mkNat' "22_2_2"
  let nHd : Option $ Nat' "Herder" := mkNat' "Herder"

  match n222 with
  | .some sn222 => IO.println s!"{(sn222 : Nat)} == 2222"
  | .none => IO.println "/_!_\\ BUG IN Nat' \"22\" clause /_!_\\"

  match nHd with
  | .some _ => IO.println "/_!_\\ BUG IN Nat' \"Herder\" clause /_!_\\"
  | .none => IO.println s!":thumbs_up:"

  IO.println s!"Let's try signed integers?"
  let ints := "-50_0"
  match mkInt' ints with
  | .some int => IO.println s!"{ints} == {(int : Int)}"
  | .none => IO.println s!"/_!_\\ BUG IN Int' {ints} clause"

  IO.println s!"Heck, we even have floats!"
  let n222d22e2 : Option $ Float' "22_2.2_2E+2" := mkFloat' "22_2.2_2E+2"
  match n222d22e2 with
  | .some sn222d22e2 => IO.println s!"My little number: Coe is magic. 222.22e2 == {(sn222d22e2 : Float) + 0.0} == 22222.0"
  | .none => IO.println "/_!_\\ BUG IN Float' \"22_2.2_2E+2\" clause /_!_\\"

  IO.println s!"Negative exponent and significand work, too!"
  let fls := "-123.45e-2"
  match mkFloat' fls with
  | .some fl => IO.println s!"{fls} == {(fl : Float)} == -1.2345"
  | .none => IO.println s!"Oh no, bug in {fls} parsing!"

  IO.println "* * *"

  -- LEB128 TESTS
  let lebx := 624485
  let blebx := ntob lebx
  /-
  5> erlang:length( "000010011000011101100101" ).
  24
  8> erlang:length("00001001").
  8
  9> erlang:length("10000111").
  8
  10> erlang:length("01100101").
  8
  11> [ 2#00001001, 2#10000111, 2#01100101 ].
  -/
  IO.println s!"{blebx} should be [9,135,101]"
  let bilebx := ByteArray.toBits blebx
  IO.println s!"{bilebx} should be 000010011000011101100101"
  let ulebx := unlead bilebx
  IO.println s!"{ulebx} should be 10011000011101100101"
  let plebx := pad7 ulebx
  IO.println s!"{plebx} should be 010011000011101100101"
  let pp := npad7 lebx
  IO.println s!"{pp} should be {plebx}"
  let fin := uLeb128 lebx
  IO.println s!"{fin} should be 229, 142, 38"
  IO.println s!"{uLeb128 1} should be 1"
  -- LE Long
  --- 00000101 11001011 10000101 11101000 11101001
  --- becomes in LE:
  --- 11101001 11101000 10000101 11001011 00000101
  ---- 233
  ---- 232
  ---- 133
  ---- 203
  ---- 5
  let bigN := 1499559017
  IO.println s!"{uLeb128 bigN} should be 233 232 133 203 5"
  IO.println s!"{reassemble $ npad7 bigN} should be 00000101 11001011 10000101 11101000 11101001"
  IO.println s!"= = = = SIGNED LEB128 TEST = = = ="
  IO.println s!"{sLeb128 (-123456)} should be [192, 187, 120]"
  IO.println s!"{sLeb128 (1)} should be [1]"
  IO.println s!"{sLeb128 (624485)} should be 229, 142, 38"
  /-
                4> 2#0000001.
                1
                5> 2#1111110.
                126
                6> 2#1111111.
                127
                7> 2#01111111.
                127
  -/
  IO.println s!"{sLeb128 (-1)} should be [127]"
  IO.println s!"{sLeb128 9000} should be 168, 198, 0 (because it's signed!)"
  IO.println s!"{uLeb128 9000} should be 70, 168"
  IO.println s!"{sLeb128 8787} should be 211, 196, 00"
  IO.println s!"= = END OF SIGNED LEB128 TEST! = ="


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
  let i := "block "
  IO.println s!"{i} is represented as:"
  void $ parseTestP blockP i
  IO.println "* * *"

  IO.println "* * *"
  let i := "(block (result i32) (i32.const 1) end)"
  IO.println s!"{i} is represented as:"
  void $ parseTestP opP i
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
      (result i32 i32) (result i32 i32)

      (block (result i32) (i32.const 1))
      (nop)
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
    let se_zero := StackEntry.num uni_num_zero
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
