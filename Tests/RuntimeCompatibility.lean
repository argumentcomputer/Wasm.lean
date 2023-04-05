import LSpec
import Megaparsec.Parsec
import Wasm.Wast.Parser
import Wasm.Bytes
import Wasm.Tests

open LSpec
open Megaparsec.Parsec
open Wasm.Wast.Parser
open Wasm.Bytes
open Wasm.Tests

/-! To test runtime compatibility between Wasm.lean engine and the reference
implementation, we choose to constrain ourselves to running only `() -> I32`
Wasm functions.
Note that our engine encodes it as `Int`, not `UInt32` at the moment.

Some discussion about this design choice can be read here:
https://github.com/yatima-inc/Wasm.lean/pull/53
 -/

partial def testGeneric : String → Int → Int → TestSeq
  | mod, os, rs =>
    let str := s!"Running function _main_ : () -> I32 evaluates the same in Lean and Rust.
    {mod}"
    test str $ os = rs

open IO.FS in
partial def runWasmTestSeq (x : String) : IO TestSeq := do
  match ←run_main x with
  | .ok y => do
    let yᵢ := y.trim.toInt!
    match parseP moduleP "test" x with
    | .error pe => pure $ test "parsing module" (ParseFailure x pe)
    | .ok m => match runModule m with
      | .ok our_y => pure $ testGeneric x our_y yᵢ
      | .error ee => pure $ test "running module" (EngineFailure x ee)
  | .error e =>
    pure $ test s!"failed to run with wasm-sandbox: {x}" (ExternalFailure e)

def basics :=
  [ "(module
        (func (export \"main\") (result i32)
          (i32.const 3555)
        )
     )"
  ]

def modsControl :=
  [
    "(module
        (func $const-i32 (result i32) (i32.const 0x132))
        (func (export \"main\") (result i32) (call $const-i32))
     )"
  , "(module
        (func $as-block-value (result i32)
          (block (result i32) (nop) (i32.const 2) (return) (i32.const 9))
        )
        (func (export \"main\") (result i32) (call $as-block-value))
     )"
  , "(module
         (func $midvalues (result i32)
          (i32.const 20) (nop) (i32.const 2) (return) (i32.const 9)
        )
        (func (export \"main\") (result i32) (call $midvalues))
     )"
  ]

def main : IO UInt32 := do
  match (← doesWasmSandboxRun?) with
  | .ok _ => withWasmSandboxRun runWasmTestSeq [ basics, modsControl ]
  | _ => withWasmSandboxFail
