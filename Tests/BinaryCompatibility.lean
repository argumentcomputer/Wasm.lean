import LSpec

open LSpec

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

def testCanary : TestSeq :=
  test "This is a canary test. Chirp chirp." true

def testCrow : TestSeq :=
  -- test "This is a crow test. Caw caw." false
  test
    "You need to have `wasm-sandbox` binary in your current work directory. Please run `wget https://github.com/cognivore/wasm-sandbox/releases/download/v1/wasm-sandbox && chmod +x ./wasm-sandbox`."
    false

def withWasmSandboxRun : IO UInt32 :=
  lspecIO $ testCanary

def withWasmSandboxFail : IO UInt32 :=
  lspecIO $ testCrow

def main : IO UInt32 := do
  match (← doesWasmSandboxRun?) with
  | Except.ok _ => withWasmSandboxRun
  | _ => withWasmSandboxFail
