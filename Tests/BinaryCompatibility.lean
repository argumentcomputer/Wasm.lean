import LSpec
import Megaparsec.Parsec
import Wasm.Wast.Parser
import Wasm.Bytes

open LSpec
open Megaparsec.Parsec
open Wasm.Wast.Parser
open Wasm.Bytes

inductive ExternalFailure (e : IO.Error) : Prop
instance : Testable (ExternalFailure e) := .isFailure s!"External failure: {e}"

open Megaparsec.Errors.Bundle in
inductive ParseFailure (src : String) (e : ParseErrorBundle Char String Unit) : Prop
instance : Testable (ParseFailure src e) := .isFailure s!"Parsing:\n{src}\n{e}"

open IO.Process (run) in
def w2b (x : String) :=
  run { cmd := "./wasm-sandbox", args := #["wast2bytes", x] } |>.toBaseIO

-- A very bad hasing function. It adds up the character codes of each of the string's characters, and then appends 'L' followed by the number of characters in the string to reduce the chance of collisions.
def myHash (s : String) : String :=
  let n := s.foldl (fun acc c => acc + c.toNat) 0
  s!"{n}L{s.length}"

def fname (s : String) : String :=
  "./wast-dump-" ++ myHash s ++ ".bytes"

/- Generic Wasm module test. -/
partial def testGeneric : String → ByteArray → ByteArray → TestSeq
  | mod, rs, os =>
    let str := s!"Binary representation is compatible with {fname mod}
    === CODE ===
    {mod}
    ||| END OF CODE |||"
    test str $ rs = os

/- Here's how Main used to test a particular module:

  IO.println s!"{i} is represented as:"
  let o_parsed_module ← parseTestP moduleP i
  match o_parsed_module.2 with
  | .error _ => IO.println "FAIL"
  | .ok parsed_module => do
    IO.println s!">>> !!! >>> It is converted to bytes as: {mtob parsed_module}"
    let f := System.mkFilePath ["/tmp", "mtob.41.wasm"]
    let h ← IO.FS.Handle.mk f IO.FS.Mode.write
    h.write $ mtob parsed_module
    gO.println "It's recorded to disk at /tmp/mtob.41.wasm"

Instead of this, here, we're going to:

 1. Make the reference WASM bytes with `wasm-sandbox` invocation,
    as provided by function `w2b`.
 2. Read the reference bytes into a variable.
 3. Compile our bytes and read those into a variable.
 4. Write our bytes into a file called s!"{fname}.lean".
 5. Byte by byte, compare the two variables, reporting errors.
-/
open IO.FS in
partial def moduleTestSeq (x : String) : IO TestSeq := do
  -- Run w2b against x
  match ←w2b x with
  | .ok _ => do
    -- Read the reference bytes into a variable.
    let ref_bytes ← readBinFile $ fname x
    -- Compile our bytes and read those into a variable.
    match parse moduleP x with
    | .error pe =>
      pure $ test "parsing module" (ParseFailure x pe)
    | .ok module => do
      let our_bytes := mtob module
      -- Write our bytes into a file called s!"{fname}.lean".
      writeBinFile s!"{fname x}.lean" our_bytes
      pure $ testGeneric x ref_bytes our_bytes
  | .error e =>
    pure $ test "failed to encode with wasm-sandbox" (ExternalFailure e)

def uWasmMods := [
  "(module
        (func (export \"main\")
            (result i32)

            (i32.add
                (i32.const 1499550000)
                (i32.add (i32.const 9000) (i32.const 17))
            )
        )
    )",
    "(module
        (func (export \"two_ints\")
            (result i32) (result i32)
            (i32.add
                (i32.const 1499550000)
                (i32.add (i32.const 9000) (i32.const 17))
            )
            (i32.add (i32.const -1) (i32.const 1))
        )
    )",
    "(module
        (func (param $x_one i32) (param $three i32) (param $y_one i32)
          (result i32) (i32.add (i32.const 40) (i32.const 2)))
        (func (param $x_two f32) (param f32) (param f32) (result i32)
          (i32.add (i32.const 12) (i32.const 30)))
    )",
    "(module
      (func (param $x i32) (param i32) (result i32)
      (i32.add (i32.const 40) (i32.const 2)))
    )",
    "(module
        ( func (param $x i32) (param i32) )
      )",
    "(module
        (func (param $x i32))
      )",
    "(module
        ( func )
      )",
    "(module)",
    "(module
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
    )",
    "(module
      (func $main (export \"main\")
        (param $x i32)
        (param $y i32)
        (result i32 i32)

        (i32.add
          (i32.const 1499550000)
          (i32.add (i32.const 17) (i32.const 9000))
        )

      )
    )"
]

def modsControl :=
  [ "(module (func) (func (nop)))"
  , "(module (func (result i32)
        (block (result i32) (i32.const 3))
     ))"
  , "(module (func (result i32)
        (if (result i32) (i32.const 0)
          (then (i32.const 1)) (else (i32.const 0))
        )
     ))"
  , "(module (func (result i32)
        (loop (result i32) (i32.const 3))
     ))"
  , "(module (func (result i64)
        (block (result i64)
          (i64.const 6)
          (i64.add (br 0))
        )
     ))"
  , "(module (func (result i32)
        (block (result i32) (i32.ctz (br_if 0)))
     ))"
  ]

open IO.Process (run) in
def doesWasmSandboxRun? :=
  run { cmd := "./wasm-sandbox", args := #["wast2bytes", "(module)"] } |>.toBaseIO

def withWasmSandboxRun : IO UInt32 :=
  let testCases := [ uWasmMods, modsControl ]
  lspecEachIO testCases.join moduleTestSeq

def withWasmSandboxFail : IO UInt32 :=
  lspecIO $ test "wasm-sandbox check"
    (ExternalFailure "You need to have `wasm-sandbox` binary in your current work directory.
    Please run:
    wget https://github.com/cognivore/wasm-sandbox/releases/download/v1/wasm-sandbox && chmod +x ./wasm-sandbox")

def main : IO UInt32 := do
  match (← doesWasmSandboxRun?) with
  | .ok _ => withWasmSandboxRun
  | _ => withWasmSandboxFail
