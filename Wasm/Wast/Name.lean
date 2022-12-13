import Straume.Zeptoparsec

import YatimaStdLib

open Cached

open Zeptoparsec

namespace Wasm.Wast.Name

/- Chars that are allowed in WASM ids. -/
def isIdChar (x : Char) : Bool :=
  x.isAlphanum || "_.+-*/\\^~=<>!?@#$%&|:'`".data.elem x

/- This is how desperate coding looks. We started with dependent parsing, and ended up here.
Well, at least we aren't using unsafe funcitons for parsing. 🤷 -/
def nameP : Parsec String String :=
  pstring "$" *> ((many $ satisfy isIdChar) >>= (pure ∘ String.mk ∘ Array.toList))

/- Captures a valid WAST identifier. -/
structure Name (x : String) where
  val : (Cached' x) := {}
  isNE : x.length ≠ 0 := by trivial
  onlyLegal : x.data.all isIdChar := by trivial
  deriving Repr

/- Perhaps, construct a valid WAST identifier. -/
def mkName (xs : String) : Option (Name xs) :=
  let xs' := xs.data
  if isNE : xs.length = 0 then
    .none
  else
    if onlyLegal : xs'.all isIdChar then
      .some { isNE, onlyLegal }
    else
      .none

end Wasm.Wast.Name
