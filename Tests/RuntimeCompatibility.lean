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

def main : IO UInt32 := do
  match (← doesWasmSandboxRun?) with
  | .ok _ => pure 0
  | _ => withWasmSandboxFail