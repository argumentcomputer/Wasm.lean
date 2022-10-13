import Wasm.Wast.BitSize
import Wasm.Wast.Radix

import Megaparsec.Common
import Megaparsec.Errors
import Megaparsec.Errors.Bundle
import Megaparsec.Parsec
import Megaparsec.MonadParsec
import YatimaStdLib.NonEmpty

open Megaparsec
open Megaparsec.Common
open Megaparsec.Errors
open Megaparsec.Errors.Bundle
open Megaparsec.Parsec
open MonadParsec
open Cached

namespace Wasm.Wast.Num

namespace NumType

/- Webassembly works on 32 and 64 bit ints and floats.
We define NumType inductive as a combination of int and float constructors with BitSize. -/
inductive NumType :=
| int : BitSize → NumType
| float : BitSize → NumType

end NumType

----------------------------------------------------
--------------------- DIGITS -----------------------
----------------------------------------------------

namespace Num.Digit

/- Decimal digits -/
def isDigit (x : Char) : Bool :=
  x.isDigit

/- Hexadecimal digits -/
def isHexdigit (x : Char) : Bool :=
  isDigit x || "AaBbCcDdEeFf".data.elem x

/- Terminal parser for digits. -/
private def parseDigit (x : Char) : Option Nat :=
  match x with
  | '0' => .some 0
  | '1' => .some 1
  | '2' => .some 2
  | '3' => .some 3
  | '4' => .some 4
  | '5' => .some 5
  | '6' => .some 6
  | '7' => .some 7
  | '8' => .some 8
  | '9' => .some 9
  | 'a' => .some 10
  | 'A' => .some 10
  | 'b' => .some 11
  | 'B' => .some 11
  | 'c' => .some 12
  | 'C' => .some 12
  | 'd' => .some 13
  | 'D' => .some 13
  | 'e' => .some 14
  | 'E' => .some 14
  | 'f' => .some 15
  | 'F' => .some 15
  | _ => .none

/- Verifiably parsed digit. -/
structure Digit (x : Char) :=
  parsed : Cached parseDigit x := {}
  doesParse : Option.isSome parsed.val := by trivial
  deriving Repr

/- Give me a parse result `pr` of parsing out a digit and a proof that it's `isSome`, and I'll give you back a natural number this digit represents. -/
def extractDigit (d : Digit x)
                 : Nat :=
  let doesParse := d.doesParse
  match prBranch : d.parsed.val with
  | .some y => y
  | .none => by simp only [prBranch] at doesParse

instance : Coe (Digit x) Nat where
  coe d := extractDigit d

--
-- Digit parsers
--

def withRangeDigitP (sat : Char → Bool) : Parsec Char String Unit Nat := do
  let ps ← getParserState
  let x ← satisfy sat
  match parseDigit x with
  | .some y => pure y
  | .none => parseError $ .trivial ps.offset .none [] -- Impossible, but it's easier than proving that c.satisfy isHexdigit → doesParse ⋯

/- Parse out a decimal digit. -/
def decDigitP : Parsec Char String Unit Nat := withRangeDigitP isDigit

/- Parse out a digit up to `f`. Case-insensitive. -/
def hexDigitP : Parsec Char String Unit Nat := withRangeDigitP isHexdigit

/- Match some `Radix` with an invocation of either `hexDigitP` or `decDigitP`. -/
def radDigitP (radix : Radix) : Parsec Char String Unit Nat :=
  match radix with
  | .ten => decDigitP
  | .sixteen => hexDigitP

end Num.Digit

----------------------------------------------------
---------------------- NATS ------------------------
----------------------------------------------------

namespace Num.Nat

open Digit

--
-- Nat parsers
--

/- Match some `Radix` with the string prefix denoting that radix. -/
def radPrefixP (radix : Radix) : Parsec Char String Unit String :=
  match radix with
  | .ten => pure $ ""
  | .sixteen => string "0x"

/- Parses a number with some decorations as per spec. -/
def radNumP (radix : Radix) : Parsec Char String Unit (List Nat) := do
  let d0 ← radDigitP radix
  let dr ← many' $ (option (oneOf ['_']) *> pure 0) *> radDigitP radix
  pure $ d0 :: dr

/- Parse a natural out of a string of some `Radix`. -/
def radixP (radix : Radix) : Parsec Char String Unit Nat := do
  let _prefix ← radPrefixP radix
  let digits ← radNumP radix
  pure $ List.foldl (fun a x => radix * a + x) 0 digits

/- Parse a decimal. -/
def decimalP : Parsec Char String Unit Nat := radixP .ten

/- Parse a hexadecimal. -/
def hexP : Parsec Char String Unit Nat := radixP .sixteen

private def demoParse (φ : Parsec Char String Unit Nat) (x : String) : Either (ParseErrorBundle Char String Unit) Nat :=
  runParserP φ "" x

/- Run a parser against `String` `y` and return a parse result. -/
def natMaybe y := do
  demoParse (radixP $ hod y) y

def parseNat' (label : String) (x : String)
  := runParserP (radixP $ hod x) label x

/- Captures a valid Natural.
If you're parsing from a file with name `name`, set `label := name`. -/
structure Nat' (x : String) where
  label : String := ""
  parsed : Cached (parseNat' label) x := {}
  doesParse : Either.isRight parsed.val := by trivial

/- If you give me a parse result `pr` and somehow manage to prove that it's `isRight`, I'll give you a `Nat`. -/
def extractNat (n : Nat' x) : Nat :=
  let doesParse := n.doesParse
  match prBranch : n.parsed.val with
  | .right y => y
  | .left _ => by
    -- unfold Either.isRight at doesParse
    -- rw [prBranch] at doesParse
    simp only [Either.isRight, prBranch] at doesParse

instance : Coe (Nat' x) Nat where
  coe n := extractNat n

/- Perhaps, construct a valid Natural.
If you're parsing from a file with name `name`, set `label := name`. -/
def mkNat' (x : String) (label : String := "") : Option (Nat' x) :=
  let pr : Cached (parseNat' label) x := {}
  if isOk : Either.isRight pr.val then
    .some {parsed := pr, label := label}
  else
    .none

end Num.Nat

----------------------------------------------------
--------------------- FLOATS -----------------------
----------------------------------------------------

namespace Num.Float

open Nat
open Digit

#eval (Radix.sixteen : Nat).toFloat

def floatRadixP (radix : Radix) : Parsec Char String Unit Float := do
  let _prefix ← radPrefixP radix
  let an ← radixP radix
  let af := an.toFloat
  let _dot ← oneOf ['.']
  let obs ← option $ radNumP radix
  let significand := af + match obs with
    | .none => 0
    | .some bs => List.foldr (fun b acc => Id.run $ do
      let rf := (radix : Nat).toFloat
      (acc / rf) + b.toFloat / rf)  0.0 bs
  let exponent ← match radix with
    | .ten => option $ oneOf "eE".data *> radDigitP .ten
    | .sixteen => option $ oneOf "pP".data *> radDigitP .ten -- I know, right? https://webassembly.github.io/spec/core/text/values.html#floating-point
  pure $ match exponent with
    | .none => significand
    | .some exp => significand * 10^(exp.toFloat)

------------------------------------------------------------------------
-- TODO: Code generation for auxiliary structures and functions?!?!?! --
------------------------------------------------------------------------

def parseFloat' (label : String) (input : String) :=
  runParserP (floatRadixP $ hod input) label input

structure Float' (x : String) where
  label : String := ""
  parsed : Cached (parseFloat' label) x := {}
  doesParse : Either.isRight parsed.val := by trivial

def extractFloat (n : Float' x) : Float :=
  let doesParse := n.doesParse
  match npBranch : n.parsed.val with
  | .right y => y
  | .left _ => by
    simp only [Either.isRight, npBranch] at doesParse

instance : Coe (Float' x) Float where
  coe n := extractFloat n

/- Perhaps, construct a valid Float.
If you're parsing from a file with name `name`, set `label := name`. -/
def mkFloat' (x : String) (label : String := "") : Option (Float' x) :=
  let pr : Cached (parseFloat' label) x := {}
  if isOk : Either.isRight pr.val then
    .some {parsed := pr, label := label}
  else
    .none

------------------------------------------------------------------------
-- TODO: Code generation for auxiliary structures and functions?!?!?! --
------------------------------------------------------------------------

end Num.Float

end Wasm.Wast.Num
