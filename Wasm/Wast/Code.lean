import Megaparsec
import Megaparsec.Common
import Megaparsec.Errors.Bundle
import Megaparsec.Parsec

import Wasm.Wast.AST
import Wasm.Wast.BitSize
import Wasm.Wast.Name
import Wasm.Wast.Num
import Wasm.Wast.Parser
import Wasm.Wast.Parser.Common

import YatimaStdLib

open Megaparsec
open Megaparsec.Common
open Megaparsec.Errors.Bundle
open Megaparsec.Parsec
open MonadParsec

open Wasm.Wast.AST
open Wasm.Wast.Name
open Wasm.Wast.Parser
open Wasm.Wast.Parser.Common
open Wasm.Wast.Num.Num.Int
open Wasm.Wast.Num.Num.Float

namespace Wasm.Wast.Code

open Local in
open Func in
def reindexParamsAndLocals (f : Func) : (List Local × List Local) :=
  let ps := reindexLocals 0 f.params
  let ls := reindexLocals (ps.length) f.locals
  (ps, ls)

