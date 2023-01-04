import Lake
open Lake DSL

package Wasm {
  precompileModules := true
}

@[default_target]
lean_lib Wasm

require LSpec from git
  "https://github.com/yatima-inc/LSpec" @ "89798a6cb76b2b29469ff752af2fd8543b3a5515"

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "f905b68f529de2af44cf6ea63489b7e3cd090050"

require Megaparsec from git
  "https://github.com/yatima-inc/Megaparsec.lean" @ "50f9beb2af165f5736155d30cdda2774784b677b"

require Yatima from git
  "https://github.com/yatima-inc/yatima-lang" @ "26e896debf14cf3bb09a7a8a00f70583ae95469d"

@[default_target]
lean_exe wasm {
  supportInterpreter := true
  root := "Main"
}
