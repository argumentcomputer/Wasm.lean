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
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "49ee890897dbdd4665d0e8c75cd3401f0b4e6f21"

require Megaparsec from git
  "https://github.com/yatima-inc/Megaparsec.lean" @ "85ffa8b5e9bd0bc9b9020fd4e0fe1baa89d69413"

@[default_target]
lean_exe wasm {
  root := "Main"
}

lean_exe Tests.Dependent
