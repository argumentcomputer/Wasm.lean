import Megaparsec.Char
import Megaparsec.Common
import Megaparsec.Parsec
import YatimaStdLib.Cached

open Cached
open Megaparsec
open Megaparsec.Common
open Megaparsec.Parsec

namespace Wasm.Wast.Name

def nameP : Parsec Char String Unit String := Char.between '\"' '\"' $
  let escapedP := single '\\' *> anySingle
  let unescapedP := noneOf "\\\"".data
  String.mk <$> many' (unescapedP <|> escapedP)


end Wasm.Wast.Name

namespace Wasm.Wast.Identifier

/- Chars that are allowed in WASM ids. -/
def isIdChar (x : Char) : Bool :=
  x.isAlphanum || "_.+-*/\\^~=<>!?@#$%&|:'`".data.elem x

/- This is how desperate coding looks. We started with dependent parsing, and ended up here.
Well, at least we aren't using unsafe funcitons for parsing. 🤷 -/
def idP : Parsec Char String Unit String :=
  single '$' *> takeWhileP .none isIdChar

/- Captures a valid WAST identifier. -/
structure Identifier (x : String) where
  val : (Cached' x) := {}
  isNE : x.length ≠ 0 := by trivial
  onlyLegal : x.data.all isIdChar := by trivial
  deriving Repr

/- Perhaps, construct a valid WAST identifier. -/
def mkIdentifier (xs : String) : Option (Identifier xs) :=
  let xs' := xs.data
  if isNE : xs.length = 0 then
    .none
  else
    if onlyLegal : xs'.all isIdChar then
      .some { isNE, onlyLegal }
    else
      .none

end Wasm.Wast.Identifier
