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

partial def testGeneric : String → Except Wasm.Engine.EngineErrors Int → Int → TestSeq
  | mod, eos, rs =>
    let str := s!"Running function _main_ : () -> I32 evaluates the same in Lean and Rust.
    === RUNTIME CODE ===
    {mod}
    ||| END OF RUNTIME CODE |||"
    match eos with
    | .ok os => test str $ os = rs
    | .error _ =>
      dbg_trace "ERROR"
      test str $ false

open IO.FS in
partial def runWasmTestSeq (x : String) : IO TestSeq := do
  match ←run_main x with
  | .ok y => do
    dbg_trace "LLLLLLLLLLLLLLLLLLLLLLL"
    dbg_trace y
    let yᵢ := y.trim.toInt!
    let our_y := run_lean_main x
    pure $ testGeneric x our_y yᵢ
  | .error _ => do
    pure $ testGeneric x (Except.error Wasm.Engine.EngineErrors.other) 0

def basics := [
  "(module
    (func (export \"main\") (result i32)
      (i32.const 3555)
    )
  )"
]

def main : IO UInt32 := do
  match (← doesWasmSandboxRun?) with
  | .ok _ => withWasmSandboxRun runWasmTestSeq [ basics ]
  | _ => withWasmSandboxFail