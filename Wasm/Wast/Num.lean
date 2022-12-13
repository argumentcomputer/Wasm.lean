import Wasm.Wast.BitSize
import Wasm.Wast.Radix
import Wasm.Wast.Sign
import Wasm.Wast.Parser.Common

import YatimaStdLib.NonEmpty

import Straume.Zeptoparsec

open Wasm.Wast.Parser.Common

open Cached

open Zeptoparsec

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

def withRangeDigitP (sat : Char → Bool) : Parsec String Nat := fun it =>
  let (x, it') := ione it sat
  match x with
  | .some xx => match parseDigit xx with
    | .some y => .success it' y
    | .none => .error it "Expected a digit, but no digit found."
  | _ => .error it "Not a digit."

/- Parse out a decimal digit. -/
def decDigitP : Parsec String Nat := withRangeDigitP isDigit

/- Parse out a digit up to `f`. Case-insensitive. -/
def hexDigitP : Parsec String Nat := withRangeDigitP isHexdigit

/- Match some `Radix` with an invocation of either `hexDigitP` or `decDigitP`. -/
def radDigitP (radix : Radix) : Parsec String Nat :=
  match radix with
  | .ten => decDigitP
  | .sixteen => hexDigitP

end Num.Digit

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
def radPrefixP (radix : Radix) : Parsec String String :=
  match radix with
  | .ten => pure $ ""
  | .sixteen => pstring "0x"

/- Parses a number with some decorations as per spec. -/
def radNumP (radix : Radix) : Parsec String (Array Nat) := do
  let d0 ← radDigitP radix
  let dr ← many $ (option (oneOf ['_']) *> pure 0) *> radDigitP radix
  pure $ Array.mk [d0] ++ dr

/- Parse a natural out of a string of some `Radix`. -/
def radixP (radix : Radix) : Parsec String Nat := do
  let _prefix ← radPrefixP radix
  let digits ← radNumP radix
  pure $ Array.foldl (fun a x => radix * a + x) 0 digits

/- Parse a decimal. -/
def decimalP : Parsec String Nat := radixP .ten

/- Parse a hexadecimal. -/
def hexP : Parsec String Nat := radixP .sixteen

private def demoParse (φ : Parsec String γ) (x : String) : Except String γ :=
  Zeptoparsec.run φ x

/- Run a parser against `String` `y` and return a parse result. -/
def natMaybe y := do
  demoParse (radixP $ hod y) y

def parseNat' (x : String)
  := Zeptoparsec.run (radixP $ hod x) x

/- Captures a valid Natural.
If you're parsing from a file with name `name`, set `label := name`. -/
structure Nat' (x : String) where
  label : String := ""
  parsed : Cached parseNat' x := {}
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
  let pr : Cached parseNat' x := {}
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

def parseInt' (x : String) :=
  let intP := do
    let sign ← signP
    let n ← radixP (hod x)
    pure $ signum sign * n
  Zeptoparsec.run intP x

/- Captures a valid signed Integer.
If you're parsing from a file with name `name`, set `label := name`. -/
structure Int' (x : String) where
  label : String := ""
  parsed : Cached parseInt' x := {}
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
  let pr : Cached parseInt' x := {}
  if isOk : Except.isOk pr.val then
    .some {parsed := pr, label := label}
  else
    .none

structure ConstInt where
  bs : BitSize
  val : Int
  deriving BEq

instance : ToString ConstInt where
  toString x := "(ConstInt " ++ toString x.bs ++ " " ++ toString x.val ++ ")"

def i32P : Parsec String ConstInt := do
    discard $ pstring "i32.const"
    ignoreP
    let ds ← many1 notSpecialP
    let dss : String := String.mk $ Array.toList ds
    -- TODO: CHECK THAT PARSED INT FITS 32 BITS
    match mkInt' dss with
    | .some i => pure $ ConstInt.mk 32 $ extractInt i
    | .none => fail "32-bit integer constant expected."

-- TODO: copypasta is bad
def i64P : Parsec String ConstInt := do
    discard $ pstring "i64.const"
    ignoreP
    let ds ← many1 notSpecialP
    let dss : String := String.mk $ Array.toList ds
    -- TODO: CHECK THAT PARSED INT FITS 64 BITS
    match mkInt' dss with
    | .some i => pure $ ConstInt.mk 64 $ extractInt i
    | .none => fail "64-bit integer constant expected."

end Num.Int

----------------------------------------------------
--------------------- FLOATS -----------------------
----------------------------------------------------

/-

Reference:
https://webassembly.github.io/spec/core/text/values.html#floating-point

TODO: represent `inf`, `nan`, and `nan:0x...`

-/

namespace Num.Float

open Nat
open Digit

def exponentP (radix : Radix) : Parsec String Int := do
  let _l ← match radix with
    | .ten => oneOf "eE".data
    | .sixteen => oneOf "pP".data
  let expsign ← signP
  let exponent ← radDigitP .ten
  pure $ signum expsign * exponent

def floatRadixP (radix : Radix) : Parsec String Float := do
  let _prefix ← radPrefixP radix
  let sign ← signP
  let s := Float.ofInt $ signum sign
  let an ← radixP radix
  let _dot ← option $ pstring "."
  let obs ← option $ radNumP radix
  let significand := s * (an.toFloat + match obs with
    | .none => 0
    | .some bs => (Array.toList bs).foldr
      (fun b acc => Id.run $ do
        let rf := (radix : Nat).toFloat
        (acc / rf) + b.toFloat / rf) 0.0)
  let exponent ← option $ exponentP radix
  pure $ match exponent, radix with
    | .none, _ => significand
    | .some exp, .ten => significand * 10^(Float.ofInt exp)
    | .some exp, .sixteen => significand * 2^(Float.ofInt exp)

------------------------------------------------------------------------
-- TODO: Code generation for auxiliary structures and functions?!?!?! --
------------------------------------------------------------------------

def parseFloat' (input : String) :=
  Zeptoparsec.run (floatRadixP $ hod input) input

structure Float' (x : String) where
  label : String := ""
  parsed : Cached parseFloat' x := {}
  doesParse : Except.isOk parsed.val := by trivial

def extractFloat (n : Float' x) : Float :=
  let doesParse := n.doesParse
  match npBranch : n.parsed.val with
  | .ok y => y
  | .error _ => by
    unfold Except.isOk at doesParse
    rw [npBranch] at doesParse
    contradiction

instance : Coe (Float' x) Float where
  coe n := extractFloat n

/- Perhaps, construct a valid Float.
If you're parsing from a file with name `name`, set `label := name`. -/
def mkFloat' (x : String) (label : String := "") : Option (Float' x) :=
  let pr : Cached parseFloat' x := {}
  if isOk : Except.isOk pr.val then
    .some {parsed := pr, label := label}
  else
    .none

structure ConstFloat where
  bs : BitSize
  val : Float
  deriving BEq

instance : ToString ConstFloat where
  toString x := "(ConstFloat " ++ toString x.bs ++ " " ++ toString x.val ++ ")"

-- TODO: copypasta is bad
def f32P : Parsec String ConstFloat := do
  discard $ pstring "f32.const"
  ignoreP
  let ds ← many1 notSpecialP
  let dss : String := String.mk $ Array.toList ds
  -- TODO: CHECK THAT PARSED FLOAT FITS 32 BITS
  match mkFloat' dss with
  | .some f => pure $ ConstFloat.mk 32 $ extractFloat f
  | .none => fail "Expected a 32-bit float."

-- TODO: copypasta is bad
def f64P : Parsec String ConstFloat := do
  discard $ pstring "f64.const"
  ignoreP
  let ds ← many1 notSpecialP
  let dss : String := String.mk $ Array.toList ds
  -- TODO: CHECK THAT PARSED FLOAT FITS 32 BITS
  match mkFloat' dss with
  | .some f => pure $ ConstFloat.mk 64 $ extractFloat f
  | .none => fail "Expected a 64-bit float"

instance : ToString ConstFloat where
  toString x := "(ConstFloat (" ++ (toString (x.bs : Nat)) ++ ") " ++ toString x.val ++ ")"

------------------------------------------------------------------------
-- TODO: Code generation for auxiliary structures and functions?!?!?! --
------------------------------------------------------------------------

end Num.Float

namespace Uni

open NumType
open Num.Int
open Num.Float

inductive NumUniT where
-- | i32 : NumType.int 32 → ConstInt → NumUniT
-- | i64 : NumType.int 64 → ConstInt → NumUniT
-- | f32 : NumType.float 32 → ConstFloat → NumUniT
-- | f64 : NumType.float 64 → ConstFloat → NumUniT
| i : ConstInt → NumUniT
| f : ConstFloat → NumUniT

end Uni

end Wasm.Wast.Num
