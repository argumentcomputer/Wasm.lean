import Lake
open Lake DSL

package Wasm

@[defaultTarget]
lean_lib Wasm

require LSpec from git
  "https://github.com/yatima-inc/LSpec.git" @ "c63610bb23451c7aa2faae17c71e8d162c6c616e"

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean.git" @ "9c362443e0d89eb96683b52a1caaf762049697c4"

require Megaparsec from git
  "https://github.com/yatima-inc/Megaparsec.lean.git/" @ "e6281377bc54ecfe94506dacfd5db3ba4277b984"

@[defaultTarget]
lean_exe wasm {
  supportInterpreter := true
  root := "Main"
}
