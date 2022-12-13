import Lake
open Lake DSL

package Wasm

@[default_target]
lean_lib Wasm

require LSpec from git
  "https://github.com/yatima-inc/LSpec" @ "89798a6cb76b2b29469ff752af2fd8543b3a5515"

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "f905b68f529de2af44cf6ea63489b7e3cd090050"

require Straume from git
  "https://github.com/yatima-inc/Straume" @ "849b7c7dc5eff27bf8cfe7e9e91d6195a7b964cb"

require Yatima from git
  "https://github.com/yatima-inc/yatima-lang" @ "26e896debf14cf3bb09a7a8a00f70583ae95469d"

@[default_target]
lean_exe wasm {
  supportInterpreter := true
  root := "Main"
}
