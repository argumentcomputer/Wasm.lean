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

def replaceNth (xs : List α) (idx : Nat) (x : α) :=
  xs.take idx ++ x :: xs.drop (idx+1)
