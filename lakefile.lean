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
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "9a49b49fc35a960ee333b47c4960390543defabd"

require Megaparsec from git
  "https://github.com/yatima-inc/Megaparsec.lean" @ "8859f129d199d5be82962140e9b886c0fd49e89c"

-- require Yatima from git
--   "https://github.com/yatima-inc/yatima-lang" @ "26e896debf14cf3bb09a7a8a00f70583ae95469d"

@[default_target]
lean_exe wasm {
  root := "Main"
}

lean_exe Tests.Dependent
lean_exe Tests.Leb128
lean_exe Tests.SimpleEncodings
lean_exe Tests.BinaryCompatibility
