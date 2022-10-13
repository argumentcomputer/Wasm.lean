import Lake
open Lake DSL

package Wasm

@[defaultTarget]
lean_lib Wasm

require LSpec from git
  "https://github.com/yatima-inc/LSpec.git" @ "c63610bb23451c7aa2faae17c71e8d162c6c616e"

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean.git" @ "02ec0ac2415f2fffcb25638553c69113d28cd47c"

require Megaparsec from git
  "https://github.com/yatima-inc/Megaparsec.lean.git/" @ "8850513e4f9d18e7c61eb0023a085422874b9120"

@[defaultTarget]
lean_exe wasm {
  supportInterpreter := true
  root := "Main"
}
