/- WAST expressions as seen in the official test suite. -/

import Wasm.Wast.BitSize
import Wasm.Wast.Name
import Wasm.Wast.Num

import Megaparsec.Common
import Megaparsec.Errors
import Megaparsec.Errors.Bundle
import Megaparsec.Parsec
import Megaparsec.MonadParsec
import YatimaStdLib.NonEmpty

open Wasm.Wast.Name
open Wasm.Wast.Num

open Megaparsec
open Megaparsec.Common
open Megaparsec.Errors
open Megaparsec.Errors.Bundle
open Megaparsec.Parsec
open MonadParsec
open Cached

namespace Wasm.Wast.Expr

structure X (xx : Nat) where
  y : Cached (fun x => Id.run do
    dbg_trace "п"
    (42 - 6) + x
  ) xx := {}
  g (t : Cached (fun x => Id.run do
    dbg_trace "x"
    36 + x
  ) xx ) := t.val

def fff x := Id.run do
  dbg_trace "o"
  42 - 6 + x

structure Xf (x : Nat) where
  y : Cached fff x := {}
  g (t : Cached fff x) : Nat := t.val
