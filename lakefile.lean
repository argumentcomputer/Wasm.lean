import Lake
open Lake DSL

package Wasm {
  precompileModules := true
}

@[default_target]
lean_lib Wasm

require LSpec from git
  "https://github.com/yatima-inc/LSpec" @ "88f7d23e56a061d32c7173cea5befa4b2c248b41"

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "533d71efa5853ff014f42c174d6321d74251209f"

require Megaparsec from git
  "https://github.com/yatima-inc/Megaparsec.lean" @ "0572258b1cfee6a399d0b867a764cee97e73a254"

-- require Yatima from git
--   "https://github.com/yatima-inc/yatima-lang" @ "26e896debf14cf3bb09a7a8a00f70583ae95469d"

@[default_target]
lean_exe wasm {
  supportInterpreter := true
  root := "Main"
}
