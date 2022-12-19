import Megaparsec.Common
import Megaparsec.MonadParsec
import Megaparsec.Parsec

open Megaparsec
open Megaparsec.Common
open Megaparsec.Parsec

/- Webassembly supports two radixes: 10 and 16, which we naively implement here by force. -/
inductive Radix :=
  | ten
  | sixteen
  deriving Repr

/- 10 *is* .ten -/
instance : OfNat Radix 10 where
  ofNat := .ten

/- 16 *is* .sixteen -/
instance : OfNat Radix 16 where
  ofNat := .sixteen

instance : ToString Radix where
  toString x := toString $ repr x

/- For something to depend on .ten means that it can just as well depend on 10. -/
instance : CoeDep Radix Radix.ten Nat where
  coe := 10

/- For something to depend on .sixteen means that it can just as well depend on 16. -/
instance : CoeDep Radix Radix.sixteen Nat where
  coe := 16

/- 10 *is* .ten and 16 *is* .sixteen -/
instance : Coe Radix Nat where
  coe x := match x with
  | .ten => 10
  | .sixteen => 16

/- We rely on numeric ordering rather than on derived ordering based on the order of constructors. -/
instance : Ord Radix where
  compare x y := Ord.compare (x : Nat) (y : Nat)

/- If something starts with "0x", then it's a hex. -/
def baseP : Parsec Char String Unit Radix :=
  (lookAhead (string "0x") *> pure .sixteen) <|> pure .ten

def isHex? (x : String) : Bool :=
  @parses? Char String Unit String (lookAhead $ string "0x") x

/-
A `Radix` constructor from `String`.

Get a string, and if it starts with "0x", return `Radix.sixteen`, otherwise, return `Radix.ten`. -/
def hod (x : String) : Radix :=
  if isHex? x then .sixteen else .ten
