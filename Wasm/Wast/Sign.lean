import Megaparsec.Common
import Megaparsec.MonadParsec
import Megaparsec.Parsec

open Megaparsec
open Megaparsec.Common
open Megaparsec.Parsec

/- Webassembly supports signed numbers. -/
inductive Sign :=
| plus
| minus

instance : ToString Sign where
  toString
    | .plus => "+"
    | .minus => "-"

instance : Coe Sign String where
  coe x := match x with
  | .plus => "+"
  | .minus => "-"

/- Turn a Sign into an Int multiplier.
Negative sign turns into -1, a positive to 1.

It's not strictly mathematical signum in that there's no 0,
but we don't need it for our purposes. -/
def signum : Sign → Int
  | .plus => 1
  | .minus => -1

/- If something starts with "-", then it's starts with a minus sign.
I am very smart.
-/
def isMinus? (x : String) : Bool :=
  @parses? Char String Unit String (lookAhead $ string "-") x

/-
A `Sign` constructor from `String`.

Get a string, and if it starts with "-", return `Sign.minus`, otherwise, return `Sign.plus`. -/
def sign (x : String) : Sign :=
  if isMinus? x then .minus else .plus

/- Parse out an optional sign. -/
def signP : Parsec Char String Unit Sign := do
  let s ← option $ string "-"
  match s with
  | .none => option (string "+") *> pure .plus
  | .some _ => pure .minus
