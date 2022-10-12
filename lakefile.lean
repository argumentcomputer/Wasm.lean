import Lake
open Lake DSL

package Wasm

@[defaultTarget]
lean_lib Wasm

require LSpec from git
  "https://github.com/yatima-inc/LSpec.git" @ "c63610bb23451c7aa2faae17c71e8d162c6c616e"

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean.git" @ "556917aefe6edd8e5f3987f601c62e7ebec66e33"

require Megaparsec from git
  "https://github.com/yatima-inc/Megaparsec.lean.git/" @ "31a592cce8920e0a8d620fb93af9909a531571a2"

@[defaultTarget]
lean_exe wasm {
  supportInterpreter := true
  root := "Main"
}
