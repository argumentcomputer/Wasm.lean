import Lake
open Lake DSL

package Wasm

require LSpec from git
  "https://github.com/yatima-inc/LSpec.git" @ "77fc51697abeff937ffd20d2050723dc0fa1c8c0"

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean.git" @ "234ee564abf64c6e45f15ed921d94a3b4db228ab"

require Straume from git
  "https://github.com/yatima-inc/straume/" @ "d8b8084bee708a230379f53ff674570153a52f0d"

@[defaultTarget]
lean_exe megaparsec {
  supportInterpreter := true
  root := "Main"
}
