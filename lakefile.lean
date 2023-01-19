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
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "649368d593f292227ab39b9fd08f6a448770dca8"

require Megaparsec from git
  "https://github.com/yatima-inc/Megaparsec.lean" @ "2e7eb85008f8bfb9d246ae0508e167e7a0de2eb3"

require Yatima from git
  "https://github.com/yatima-inc/yatima-lang" @ "517ec2f8fa7c5bcd0bccafc96c28eb81a8f1dbf0"

@[default_target]
lean_exe wasm {
  supportInterpreter := true
  root := "Main"
}

lean_exe Tests.Dependent
