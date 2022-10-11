/- WAST expressions as seen in the official test suite. -/

import Megaparsec.Char
import Megaparsec.Common
import Megaparsec.Errors
import Megaparsec.Errors.Bundle
import Megaparsec.String
import Megaparsec.Parsec
import Megaparsec.MonadParsec
import YatimaStdLib.NonEmpty

open Megaparsec.Char
open Megaparsec.Common
open Megaparsec.Errors
open Megaparsec.Errors.Bundle
open Megaparsec.String
open Megaparsec.Parsec
open MonadParsec
open List

namespace Wasm.Wast.Expr

/- TODO: Move to SDLIB -/
/- TODO: Make MemoF which memoises a function call so that we have the result available without re-computing. -/
structure Cached {α : Type u} (a : α) :=
  val : α
  proof : val = a
  deriving Repr

instance : EmptyCollection (Cached a) where emptyCollection := ⟨a, rfl⟩
instance : Inhabited (Cached a) where default := {}
instance : Subsingleton (Cached a) where
  allEq := fun ⟨b, hb⟩ ⟨c, hc⟩ => by subst hb; subst hc; rfl
instance : DecidableEq (Cached a) := fun _ _ => isTrue (Subsingleton.allEq ..)

structure Memo {α : Type u} {β : Type v} (x : α) (f : α → β) :=
  val : β
  isFX : f x = val

instance : EmptyCollection (Memo x f) where emptyCollection := ⟨ f x, rfl ⟩
instance : Inhabited (Memo x f) where default := {}
instance : Subsingleton (Memo x f) where
  allEq := fun ⟨b, hb⟩ ⟨c, hc⟩ => by subst hb; subst hc; rfl
instance : DecidableEq (Cached a) := fun _ _ => isTrue (Subsingleton.allEq ..)

structure X (xx : Nat) where
  y : Memo xx (fun x => Id.run do
    dbg_trace "п"
    (42 - 6) + x
  ) := {}
  g (t : Memo xx (fun x => Id.run do
    dbg_trace "x"
    36 + x
  )) := t.val

def fff x := Id.run do
  dbg_trace "o"
  42 - 6 + x

structure Xf (x : Nat) where
  y : Memo x fff := {}
  g (t : Memo x fff) : Nat := t.val

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

/- Webassembly supports two radixes: 10 and 16, which we naively implement here by force. -/
inductive Radix :=
| ten
| sixteen

/- 10 *is* .ten -/
instance : OfNat Radix 10 where
  ofNat := .ten

/- 16 *is* .sixteen -/
instance : OfNat Radix 16 where
  ofNat := .sixteen

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

/- Decimal digits -/
def isDigit (x : Char) : Bool :=
  x.isDigit

/- Hexadecimal digits -/
def isHexdigit (x : Char) : Bool :=
  isDigit x || "AaBbCcDdEeFf".data.elem x

/- Oldschool megaparsec bundles. TODO: Refactor to ergonomic version. -/
def s := string_simple_pure
/- Oldschool megaparsec bundles. TODO: Refactor to ergonomic version. -/
def c := char_simple_pure

/- Terminal parser for digits. -/
private def parseDigit (x : Char) : Option Nat :=
  dbg_trace "d"
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

/- Give me a parse result `pr` of parsing out a digit and a proof that it's `isSome`, and I'll give you back a natural number this digit represents. -/
def extractDigit (pr : Memo x parseDigit)
                 (doesParse : ∃ arg : Memo x parseDigit, Option.isSome arg.val)
                 : Nat :=
  match prBranch : pr.val with
  | .some y => y
  | .none => by
    have : False :=
      Exists.elim doesParse (fun earg =>
        fun isSomeHypothesis => by
          simp only [Subsingleton.elim earg pr, prBranch, Option.isSome] at isSomeHypothesis
      )
    contradiction

/- Verifiably parsed digit. -/
structure Digit (x : Char) :=
  parsed : Memo x parseDigit := {}
  doesParse : (∃ arg : Memo x parseDigit, Option.isSome arg.val)
  val (arg : Memo x parseDigit) : Nat := extractDigit arg doesParse

/- Parse out a digit up to `f`. Case-insensitive. -/
def digitP : Parsec Char String Unit Nat := do
  let ps ← s.getParserState
  let x ← c.satisfy isHexdigit
  match parseDigit x with
  | .some y => pure y
  | .none => s.parseError $ .trivial ps.offset .none [] -- Impossible, but it's easier than proving that c.satisfy isHexdigit → doesParse ⋯

/- Parse out a decimal digit. -/
def decDigitP : Parsec Char String Unit Nat := do
  let ps ← s.getParserState
  let y ← digitP
  if y ≥ 10 then
    s.parseError $ .trivial ps.offset .none [.tokens (toNEList '0' ['1', '2', '3', '4', '5', '6', '7', '8', '9'])]
  else
    pure y

/- An alias for `digitP`. -/
def hexDigitP : Parsec Char String Unit Nat := digitP

/- Match some `Radix` with an invocation of either `hexDigitP` or `decDigitP`. -/
def radDigitP (radix : Radix) : Parsec Char String Unit Nat :=
  match radix with
  | .ten => decDigitP
  | .sixteen => hexDigitP

-- https://github.com/leanprover/lean4/issues/1573
mutual
  partial def someP (p : Parsec Char String Unit γ) : Parsec Char String Unit (List γ) := do
    let y ← p
    let ys ← manyP p
    pure $ y :: ys
  partial def manyP (p : Parsec Char String Unit γ) : Parsec Char String Unit (List γ) := do
    someP p <|> pure []
  partial def sepEndBy1P (p : Parsec Char String Unit γ) (sep : Parsec Char String Unit γ') := do
    let y ← p
    let ys ← (sep *> sepEndByP p sep)
    pure $ y :: ys
  partial def sepEndByP (p : Parsec Char String Unit γ) (sep : Parsec Char String Unit γ') :=
    sepEndBy1P p sep <|> pure []
end

/- Match some `Radix` with the string prefix denoting that radix. -/
def radDigitPrefixP (radix : Radix) : Parsec Char String Unit String :=
  match radix with
  | .ten => pure $ ""
  | .sixteen => s.stringP "0x"

/- Parse a natural out of a string of some `Radix`. -/
def radixP (radix : Radix) : Parsec Char String Unit Nat := do
  let _prefix ← radDigitPrefixP radix
  let digits ← someP $ radDigitP radix
  pure $ foldl (fun a x => radix * a + x) 0 digits

/- Parse a decimal. -/
def decimalP : Parsec Char String Unit Nat := radixP .ten

/- Parse a hexadecimal. -/
def hexP : Parsec Char String Unit Nat := radixP .sixteen

/- If something starts with "0x", then it's a hex. -/
def isHex? (x : String) : Bool :=
  parses? (s.lookAhead $ s.stringP "0x") x

/-
A `Radix` constructor from `String`.

Get a string, and if it starts with "0x", return `Radix.sixteen`, otherwise, return `Radix.ten`. -/
def hod (x : String) : Radix :=
  if isHex? x then .sixteen else .ten

private def demoParse (φ : Parsec Char String Unit Nat) (x : String) : Either (ParseErrorBundle Char String Unit) Nat :=
  runParserP φ "" x

/- Run a parser against `String` `y` and return a parse result. -/
def natMaybe y := do
  demoParse (radixP $ hod y) y

/- If you give me a parse result `pr` and somehow manage to prove that it's `isRight`, I'll give you a `Nat`. -/
def extractNat (pr : Cached (natMaybe x))
               (doesParse : ∃ arg : Cached (natMaybe x), Either.isRight arg.val)
               : Nat :=
  match h : pr.val with
  | .right y => y
  | .left _ => by
      have : False :=
        Exists.elim doesParse (fun earg =>
          fun isRightHypothesis => by
            simp only [Subsingleton.elim earg pr, h, Either.isRight] at isRightHypothesis
          )
      contradiction

/- An un-verified way to parse out a natural number. -/
-- structure PNat' (x : String) :=
--   parsed : Cached (natMaybe x) := {}
--   val : Nat

/- Captures a valid Natural. -/
structure Nat' (xs : String) where


/- Chars that are allowed in WASM ids. -/
def isIdChar (x : Char) : Bool :=
  x.isAlphanum || "_.+-*/\\^~=<>!?@#$%&|:'`".data.elem x

-- def tt := natMaybe "0xff"
-- #eval match tt with
-- | .left x => s!"{x}"
-- | .right y => s!"{y}"

-- def mtt : Cached (natMaybe "23") := {}
-- #eval match mtt.val with
-- | .right x => s!"{x}"
-- | .left y => s!"{y}"

/- Captures a valid identifier.
-/
structure Name (x : String) where
  val : (Cached x) := {}
  isNE : x.length ≠ 0 := by trivial
  onlyLegal : x.data.all isIdChar := by trivial
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
