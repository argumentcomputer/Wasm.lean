/- WAST expressions as seen in the official test suite. -/

import Megaparsec.Char
import Megaparsec.Common
import Megaparsec.String
import Megaparsec.Parsec

open Megaparsec.Char
open Megaparsec.Common
open Megaparsec.String
open Megaparsec.Parsec

namespace Wasm.Wast.Expr

/-- `Fin n` is a natural number `i` with the constraint that `0 ≤ i < n`.
structure Fin (n : Nat) where
  val  : Nat
  isLt : LT.lt val n
-/

-- add

/- Webassembly works on 32 and 64 bit ints and floats.
We define BitSize inductive to then combine it with respective constructors. -/
inductive BitSize :=
| thirtyTwo
| sixtyFour
deriving BEq


-- Boring instances

/- 32 *is* .thirtyTwo -/
instance : OfNat BitSize 32 where
  ofNat := .thirtyTwo

/- 64 *is* .sixtyFour -/
instance : OfNat BitSize 64 where
  ofNat := .sixtyFour

/- For something to depend on .thirtyTwo means that it can just as well depend on 32. -/
instance : CoeDep BitSize BitSize.thirtyTwo Nat where
  coe := 32

/- For something to depend on .sixtyFour means that it can just as well depend on 64. -/
instance : CoeDep BitSize BitSize.sixtyFour Nat where
  coe := 64

/- 32 *is* .thirtyTwo and 64 *is* .sixtyFour -/
instance : Coe BitSize Nat where
  coe x := match x with
  | .thirtyTwo => 32
  | .sixtyFour => 64

/- We rely on numeric ordering rather than on derived ordering based on the order of constructors. -/
instance : Ord BitSize where
  compare x y := Ord.compare (x : Nat) (y : Nat)

-- End of boring instances

/- Webassembly works on 32 and 64 bit ints and floats.
We define NumType inductive as a combination of int and float constructors with BitSize. -/
inductive NumType :=
| int : BitSize → NumType
| float : BitSize → NumType

def isDigit (x : Char) : Bool :=
  x.isDigit

def isHexdigit (x : Char) : Bool :=
  isDigit x || "AaBbCcDdEeFf".data.elem x

def s := string_simple_pure
def c := char_simple_pure

private def parseDigit (p : Char → Bool) : Parsec Char String Unit (List Nat × Nat × Nat) := do
   let accradmul ← s.getParserState
   let y ← c.satisfy p
  --  let a := c2ia y accradmul
   sorry

private def parseRadixNat'Do (x : String) (radix : Nat) : (List Nat × Nat × Nat) :=
  ([0], radix, 0)

def parseRadixNat' (x : String) (radix := 10) : Nat :=
  List.foldl (fun x y => x + y) 0 (parseRadixNat'Do ((String.mk ∘ List.reverse) x.data) radix).1

def isHex (x : String) : Bool :=
  parses? (s.lookAhead $ s.stringP "0x") x

structure Nat' (x : String) :=
  val : Nat := parseRadixNat' x (if isHex x then 16 else 10)

def isIdChar (x : Char) : Bool :=
  x.isAlphanum || "_.+-*/\\^~=<>!?@#$%&|:'`".data.elem x

/- Captures a valid identifier.
-/
structure Name (x : String) where
  val : String := x
  isNE : x.length ≠ 0
  onlyLegal : x.data.all isIdChar
  deriving Repr

def mkName (xs : String) : Option (Name xs) :=
  let xs' := xs.data
  if isNE : xs.length = 0 then
    .none
  else
    if onlyLegal : xs'.all isIdChar then
      .some { isNE, onlyLegal }
    else
      .none
