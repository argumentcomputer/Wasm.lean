import Lake
open Lake DSL

package Wasm

@[default_target]
lean_lib Wasm

require LSpec from git
  "https://github.com/yatima-inc/LSpec.git" @ "02e423d02d2ba1b76bed3cf6459a5c2d7a13afb8"

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean.git" @ "b6b2ff88d06b3c200b9b81aa0a0ac952c35e4631"

require Megaparsec from git
  "https://github.com/yatima-inc/Megaparsec.lean.git/" @ "50f9beb2af165f5736155d30cdda2774784b677b"

@[default_target]
lean_exe wasm {
  supportInterpreter := true
  root := "Main"
}
