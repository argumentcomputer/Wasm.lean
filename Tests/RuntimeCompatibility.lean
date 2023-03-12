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

/--
open IO.FS in
partial def runWasmTestSeq (x : String) : IO TestSeq := do
  match ←run_main x with
  | .ok y => do
    let yᵢ := y.toInt!
    let our_y := run_lean_main x
  | .error _ => do
    pure sorry
--/

def main : IO UInt32 := do
  match (← doesWasmSandboxRun?) with
  | .ok _ => pure 0
  | _ => withWasmSandboxFail