import Lake
open Lake DSL

package Wasm

@[default_target]
lean_lib Wasm

require LSpec from git
  "https://github.com/yatima-inc/LSpec.git" @ "02e423d02d2ba1b76bed3cf6459a5c2d7a13afb8"

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean.git" @ "2b914196a8c67838e63c1c1e44eaf339b8a50eb7"

require Megaparsec from git
  "https://github.com/yatima-inc/Megaparsec.lean.git/" @ "e9238a79b3bef1be1bc1e99f26acc189bec12542"

@[default_target]
lean_exe wasm {
  supportInterpreter := true
  root := "Main"
}
