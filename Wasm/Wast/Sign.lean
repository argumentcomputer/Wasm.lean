import Wasm.Wast.Parser.Common

import Straume.Zeptoparsec

open Wasm.Wast.Parser.Common

open Zeptoparsec

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
  match x.data with
  | x :: _ => x == '-'
  | _ => false

/-
A `Sign` constructor from `String`.

Get a string, and if it starts with "-", return `Sign.minus`, otherwise, return `Sign.plus`. -/
def sign (x : String) : Sign :=
  if isMinus? x then .minus else .plus

/- Parse out an optional sign. -/
def signP : Parsec String Sign := do
  let s ← option $ pstring "-"
  match s with
  | .none => option (pstring "+") *> pure .plus
  | .some _ => pure .minus
