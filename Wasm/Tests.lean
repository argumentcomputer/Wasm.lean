import LSpec
import Megaparsec.Errors.Bundle
import Megaparsec.Parsec
import Wasm.Engine
import Wasm.Wast.AST
import Wasm.Wast.Parser
import Wasm.Bytes

open LSpec
open Megaparsec.Errors.Bundle
open Megaparsec.Parsec
open Wasm.Engine
open Wasm.Wast.AST.Module
open Wasm.Wast.Parser
open Wasm.Bytes

namespace Wasm.Tests

inductive ExternalFailure (e : IO.Error) : Prop
instance : Testable (ExternalFailure e) := .isFailure s!"External failure: {e}"

open Megaparsec.Errors.Bundle in
inductive ParseFailure (src : String) (e : ParseErrorBundle Char String Unit) : Prop
instance : Testable (ParseFailure src e) := .isFailure s!"Parsing:\n{src}\n{e}"

inductive EngineFailure (src : String) (e : EngineErrors) : Prop
instance : Testable (EngineFailure src e) :=
  .isFailure s!"Engine failure: {e}\n=================\n{src}"


open IO.Process (run) in
def w2b (x : String) :=
  run { cmd := "./wasm-sandbox", args := #["wast2bytes", x] } |>.toBaseIO

open IO.Process (run) in
def run_main (x : String) :=
  run { cmd := "./wasm-sandbox", args := #["run_main", x] } |>.toBaseIO

def runModule (m : Module) : Except EngineErrors Int := do
  let store := mkStore m
  let s₀ := Stack.mk []
  match exportedFidByName store "main" with
  | .none => .error $ .function_not_found (.by_name "main")
  | .some fid =>
    run store fid s₀ >>= fun (_, s₁) =>
      match s₁ with
      | ⟨ [y] ⟩ => match y with
        | .num (.i ⟨32, n⟩) => pure n
        | _ => Except.error EngineErrors.typecheck_failed
      | _ => Except.error EngineErrors.stack_incompatible_with_results


/-- A very bad hashing function. It adds up the character codes of each of the string's characters, and then appends 'L' followed by the number of characters in the string to reduce the chance of collisions. -/
def badHash (s : String) : String :=
  let n := s.foldl (fun acc c => acc + c.toNat) 0
  s!"{n}L{s.length}"

def dumpFname (s : String) : String :=
  "./wast-dump-" ++ badHash s ++ ".bytes"

open IO.Process (run) in
def doesWasmSandboxRun? :=
  (
    run { cmd := "./wasm-sandbox", args := #["wast2bytes", "(module)"] } *>
    run { cmd := "./wasm-sandbox", args := #["run_main", "(module (func (export \"main\") (result i32) (i32.const 42)))"] }
  ) |>.toBaseIO

def withWasmSandboxRun (a2t : String → IO TestSeq) (testCases : List $ List String) : IO UInt32 :=
  lspecEachIO testCases.join a2t

def withWasmSandboxFail : IO UInt32 :=
  lspecIO $ test "wasm-sandbox check"
    (ExternalFailure "You need to have `wasm-sandbox` binary in your current work directory.
    Please run:
    wget https://github.com/cognivore/wasm-sandbox/releases/download/v1/wasm-sandbox && chmod +x ./wasm-sandbox
    Or build it from source:
    git clone https://github.com/cognivore/wasm-sandbox.git wsrepo && cd wsrepo && cargo build --release && cp target/release/wasm-sandbox ../ && cd .. && rm -rf wsrepo")
