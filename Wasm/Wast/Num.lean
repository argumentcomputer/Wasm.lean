import Wasm.Wast.BitSize
import Wasm.Wast.Radix
import Wasm.Wast.Sign
import Wasm.Wast.Parser.Common

import Megaparsec.Common
import Megaparsec.Errors
import Megaparsec.Errors.Bundle
import Megaparsec.Parsec
import Megaparsec.MonadParsec
import YatimaStdLib.Cached
import YatimaStdLib.NonEmpty

open Wasm.Wast.Parser.Common

open Megaparsec
open Megaparsec.Common
open Megaparsec.Errors
open Megaparsec.Errors.Bundle
open Megaparsec.Parsec
open MonadParsec
open Cached

def toNBits (i : Int) (size : BitSize := 64) : List Bit :=
  let bits := i.toBits
  let padbit := if i ≥ 0 then .zero else .one
  List.replicate (size - bits.length) padbit ++ bits

instance : Repr ByteArray where
  reprPrec bs _ := ByteArray.toHexString bs

namespace Wasm.Wast.Num

namespace NumType

/- Webassembly works on 32 and 64 bit ints and floats.
We define NumType inductive as a combination of int and float constructors with BitSize. -/
inductive NumType :=
| int : BitSize → NumType

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
  | .none => parseError $ .trivial ps.offset .none $ hints0 Char

/- Parse out a decimal digit. -/
def decDigitP : Parsec Char String Unit Nat := withRangeDigitP isDigit

/- Parse out a digit up to `f`. Case-insensitive. -/
def hexDigitP : Parsec Char String Unit Nat := withRangeDigitP isHexdigit

/- Match some `Radix` with an invocation of either `hexDigitP` or `decDigitP`. -/
def radDigitP (radix : Radix) : Parsec Char String Unit Nat :=
  match radix with
  | .ten => decDigitP
  | .sixteen => hexDigitP

def mkDigit (y : Char) (_label : String := "") : Option (Digit y) :=
  let pr : Cached Wasm.Wast.Num.Num.Digit.parseDigit y := {}
  if isOk : Option.isSome pr.val then
    let d : Digit y := { parsed := pr }
    .some d
  else
    .none

end Num.Digit
open Num.Digit

----------------------------------------------------
---------------------- NATS ------------------------
----------------------------------------------------

/-

Reference:
https://webassembly.github.io/spec/core/text/values.html#floating-point

`Nat'`s are unsigned.

-/

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

/- Parse a natural out of a string. Infer Radix based on parsec state -/
def natP : Parsec Char String Unit Nat := do
  let ps ← getParserState
  radixP $ hod ps.input

/- Parse a decimal. -/
def decimalP : Parsec Char String Unit Nat := radixP .ten

/- Parse a hexadecimal. -/
def hexP : Parsec Char String Unit Nat := radixP .sixteen

private def demoParse (φ : Parsec Char String Unit γ) (x : String) : Except (ParseErrorBundle Char String Unit) γ :=
  runParserP φ "" x

/- Run a parser against `String` `y` and return a parse result. -/
def natMaybe y := do
  demoParse natP y

def parseNat' (label : String) (x : String)
  := runParserP natP label x

/- Captures a valid Natural.
If you're parsing from a file with name `name`, set `label := name`. -/
structure Nat' (x : String) where
  label : String := ""
  parsed : Cached (parseNat' label) x := {}
  doesParse : Except.isOk parsed.val := by trivial

/- If you give me a parse result `pr` and somehow manage to prove that it's `isRight`, I'll give you a `Nat`. -/
def extractNat (n : Nat' x) : Nat :=
  let doesParse := n.doesParse
  match prBranch : n.parsed.val with
  | .ok y => y
  | .error _ => by
    unfold Except.isOk at doesParse
    rw [prBranch] at doesParse
    -- simp only [isOk, prBranch] at doesParse
    contradiction

instance : Coe (Nat' x) Nat where
  coe n := extractNat n

/- Perhaps, construct a valid Natural.
If you're parsing from a file with name `name`, set `label := name`. -/
def mkNat' (x : String) (label : String := "") : Option (Nat' x) :=
  let pr : Cached (parseNat' label) x := {}
  if isOk : Except.isOk pr.val then
    .some {parsed := pr, label := label}
  else
    .none

end Num.Nat

----------------------------------------------------
---------------------- INTS ------------------------
----------------------------------------------------

/-

Reference:
https://webassembly.github.io/spec/core/text/values.html#integers

`Int'` is just a signed `Nat'`.

-/

namespace Num.Int

open Num.Nat

def parseInt' (label : String) (x : String) :=
  let intP := do
    let sign ← signP
    -- hod is bugged because it doesn't work on strings with minus prefix
    let n ← natP
    eof -- the spec requires that the whole number is well-formed
    pure $ signum sign * n
  runParserP intP label x

/- Captures a valid signed Integer.
If you're parsing from a file with name `name`, set `label := name`. -/
structure Int' (x : String) where
  label : String := ""
  parsed : Cached (parseInt' label) x := {}
  doesParse : Except.isOk parsed.val := by trivial

/- If you give me a parse result `pr` and somehow manage to prove that it's `isRight`, I'll give you a `Int`. -/
def extractInt (n : Int' x) : Int :=
  let doesParse := n.doesParse
  match prBranch : n.parsed.val with
  | .ok y => y
  | .error _ => by
    unfold Except.isOk at doesParse
    rw [prBranch] at doesParse
    contradiction
    -- simp only [Either.isRight, prBranch] at doesParse

instance : Coe (Int' x) Int where
  coe n := extractInt n

/- Perhaps, construct a valid Integer.
If you're parsing from a file with name `name`, set `label := name`. -/
def mkInt' (x : String) (label : String := "") : Option (Int' x) :=
  let pr : Cached (parseInt' label) x := {}
  if isOk : Except.isOk pr.val then
    .some {parsed := pr, label := label}
  else
    .none

structure ConstInt where
  bs : BitSize
  val : Int
  deriving BEq

instance : ToString ConstInt where
  toString x := "(ConstInt.mk " ++ toString x.bs ++ " " ++ toString x.val ++ ")"

def iP : Parsec Char String Unit ConstInt := do
  let bs ← string "i32.const" <|> string "i64.const"
  ignoreP
  let ps ← getParserState
  let ds ← many1' notSpecialP
  -- TODO: CHECK THAT PARSED INT FITS THE N BITS
  match mkInt' ⟨ds⟩ with
  | .some i =>
    let nbs := if bs = "i32.const" then 32 else 64
    pure $ ConstInt.mk nbs $ extractInt i
  | .none => parseError $ .trivial ps.offset .none $ hints0 Char

end Num.Int

namespace Uni

open NumType
open Num.Int

inductive NumUniT where
| i : ConstInt → NumUniT
  deriving BEq

instance : ToString NumUniT where
  toString | .i ci => s!"(NumUniT.i {ci})"

def numUniTP : Parsec Char String Unit NumUniT :=
  .i <$> iP

end Uni

/-- Parse a byte, with or without a `0x` prefix. -/
def uint8P (prefix? : Bool := true) : Parsec Char String Unit UInt8 := do
  if prefix? then discard $ string "0x"
  let d1 ← hexDigitP
  let d2 ← option' hexDigitP
  match d2 with
  | .some dn => pure (d1 * 16 + dn).toUInt8
  | .none => pure d1.toUInt8

/-- Parse a bytearray from a string of hexform bytes, e.g. `ceb0`. -/
def bytesFromHexP : Parsec Char String Unit ByteArray :=
  (ByteArray.mk ∘ Array.mk) <$> many' (uint8P false) <* eof

end Wasm.Wast.Num
