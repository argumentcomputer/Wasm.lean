import LSpec
import Megaparsec.Parsec
import Wasm.Wast.Parser
import Wasm.Bytes

open LSpec
open Megaparsec.Parsec
open Wasm.Wast.Parser
open Wasm.Bytes

-- Success and failure
structure Success where
  stdout : String
  stderr : String

structure Failure where
  stdout : String
  stderr : String
  exitCode : UInt32

structure Fault where
  error : IO.Error

def run (args : IO.Process.SpawnArgs) : IO $ Except (Except Fault Failure) Success := do
  match (← IO.Process.output args |>.toBaseIO) with
  | .ok out =>
    if out.exitCode = 0 then
      pure $ Except.ok $ Success.mk out.stdout out.stderr
    else
      pure $ Except.error $ Except.ok $ Failure.mk out.stdout out.stderr out.exitCode
  | .error err =>
      pure $ Except.error $ Except.error $ Fault.mk err

def doesWasmSandboxRun? := do
  run { cmd := "./wasm-sandbox", args := #["wast2bytes", "(module)"] }

def w2b (x : String) := do
  run { cmd := "./wasm-sandbox", args := #["wast2bytes", x] }

def testCanary : TestSeq :=
  test "This is a canary test. Chirp chirp." true

def testCrow : TestSeq :=
  -- test "This is a crow test. Caw caw." false
  test
    "You need to have `wasm-sandbox` binary in your current work directory. Please run `wget https://github.com/cognivore/wasm-sandbox/releases/download/v1/wasm-sandbox && chmod +x ./wasm-sandbox`."
    false

-- A very bad hasing function. It adds up the character codes of each of the string's characters, and then appends 'L' followed by the number of characters in the string to reduce the chance of collisions.
def myHash (s : String) : String :=
  let n := s.foldl (fun acc c => acc + c.toNat) 0
  s!"{n}L{s.length}"

def fname (s : String) : String :=
  "./wast-dump-" ++ myHash s ++ ".bytes"

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
        (func (param $x_one i32) (param $three i32) (param $y_one i32) (result i32) (i32.add (i32.const 40) (i32.const 2)))
        (func (param $x_two f32) (param f32) (param f32) (result i32) (i32.add (i32.const 12) (i32.const 30)))
    )",
    "(module
      (func (param $x i32) (param i32) (result i32) (i32.add (i32.const 40) (i32.const 2)))
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
        (param $y i32)
        (param i32)
        (result i32 i32)

        (i32.add
          (i32.const 1499550000)
          (i32.add (i32.const 17) (i32.const 9000))
        )

      )
    )",
    "(module (func (result i32)
        (block (result i32) (i32.const 3))
    ))"

]

-- TODO: Prove termination because lengths decrease 1 at a time.
-- Byte by byte, compare the two variables, reporting errors.
partial def loop (rs : ByteArray) (os : ByteArray) : Bool :=
  let il := os.data.toList
  let jl := rs.data.toList
  -- Let's see if the lengths aren't the same. If they aren't, we're done.
  match il.length != jl.length with
  | true => false
  | false => Id.run $ do
      -- If they are, let's compare the two lists.
      match (il, jl) with
      | ([], []) => true
      | (i::is, j::js) => do
        if i ≠ j then
          false
        else
          loop (ByteArray.mk $ Array.mk js) (ByteArray.mk $ Array.mk is)
      | _ => false

/- Generic Wasm module test that uses loop to check for stuff. -/
partial def testGeneric : String → ByteArray → ByteArray → TestSeq
  | mod, rs, os => test s!"Binary representation is compatible with {fname mod}\n=== CODE ===\n{mod}\n||| END OF CODE |||" $ loop rs os

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

 1. Make the reference WASM bytes with `wasm-sandbox` invocation, as provided by function `w2b`.
 2. Read the reference bytes into a variable.
 3. Compile our bytes and read those into a variable.
 4. Write our bytes into a file called s!"{fname}.lean".
 5. Byte by byte, compare the two variables, reporting errors.
-/
partial def moduleTestIO (x : String) : IO UInt32 := do
  -- Run w2b against x
  -- If we failed for any reason, we return false, otherwise, we go ahead to the next step, encoded as another function.
  match (← w2b x) with
  | .error _ =>
    pure 35
  | .ok _w2b_x => do
    -- Read the reference bytes into a variable.
    let ref_bytes ← IO.FS.Handle.mk (fname x) IO.FS.Mode.read >>= fun h => h.readBinToEnd
    -- Compile our bytes and read those into a variable.
    let o_parsed_module := parseP moduleP "" x
    match o_parsed_module with
    | .error _ =>
      pure 55
    | .ok parsed_module => do
      let our_bytes := mtob parsed_module
      -- Write our bytes into a file called s!"{fname}.lean".
      let h ← IO.FS.Handle.mk s!"{fname x}.lean" IO.FS.Mode.write
      h.write our_bytes
      lspecIO $ testGeneric x ref_bytes our_bytes

def withWasmSandboxRun : IO UInt32 :=
  -- For each element in uWasmMods, run moduleTestIO on it.
  uWasmMods.foldlM (fun _ x => moduleTestIO x) 0

def withWasmSandboxFail : IO UInt32 :=
  lspecIO $ testCrow

def main : IO UInt32 := do
  match (← doesWasmSandboxRun?) with
  | Except.ok _ => withWasmSandboxRun
  | _ => withWasmSandboxFail
