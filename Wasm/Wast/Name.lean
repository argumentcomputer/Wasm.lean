import YatimaStdLib

open Cached

namespace Wasm.Wast.Name

/- Chars that are allowed in WASM ids. -/
def isIdChar (x : Char) : Bool :=
  x.isAlphanum || "_.+-*/\\^~=<>!?@#$%&|:'`".data.elem x

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
