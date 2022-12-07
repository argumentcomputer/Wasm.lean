import Megaparsec.MonadParsec
import Megaparsec.Common
import Megaparsec.Errors

open MonadParsec
open Megaparsec.Parsec
open Megaparsec.Common
open Megaparsec.Errors

namespace Wasm.Wast.Parser.Common

def ignoreP : Parsec Char String Unit Unit :=
  discard $ some' $ oneOf " \t\n".data

def owP : Parsec Char String Unit Unit :=
  discard $ many' $ oneOf " \t\n".data

def specials : List Char := " ()".data

def notSpecialP : Parsec Char String Unit Char :=
  noneOf specials

def hints0 (β : Type u) [Ord β] : Std.RBSet (ErrorItem β) Ord.compare :=
  Std.mkRBSet (ErrorItem β) Ord.compare

def optional (x : Option α) (d : α) : α :=
    match x with
    | .none => d
    | .some y => y
