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
structure Memo {α : Type u} (a : α) :=
  val : α
  proof : val = a

instance : EmptyCollection (Memo a) where emptyCollection := ⟨a, rfl⟩
instance : Inhabited (Memo a) where default := {}
instance : Subsingleton (Memo a) where
  allEq := fun ⟨b, hb⟩ ⟨c, hc⟩ => by subst hb; subst hc; rfl
instance : DecidableEq (Memo a) := fun _ _ => isTrue (Subsingleton.allEq ..)

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

private def extractDigit (pr : Memo (parseDigit x))
                         (doesParse : ∃ arg : Memo (parseDigit x), Option.isSome arg.val)
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

/- Verifiably parsed digit. I don't think we need it, but it's nice to have. -/
structure Digit (x : Char) :=
  parsed : Memo (parseDigit x) := {}
  doesParse : (∃ arg : Memo (parseDigit x), Option.isSome arg.val)
  vall (arg : Memo (parseDigit x)) : Nat := extractDigit arg doesParse

def digitP : Parsec Char String Unit Nat := do
  let ps ← s.getParserState
  let x ← c.satisfy isHexdigit
  match parseDigit x with
  | .some y => pure y
  | .none => s.parseError $ .trivial ps.offset .none [] -- Impossible, but it's easier than proving that c.satisfy isHexdigit → doesParse ⋯

def decDigitP : Parsec Char String Unit Nat := do
  let ps ← s.getParserState
  let y ← digitP
  if y ≥ 10 then
    s.parseError $ .trivial ps.offset .none [.tokens (toNEList '0' ['1', '2', '3', '4', '5', '6', '7', '8', '9'])]
  else
    pure y

def hexDigitP : Parsec Char String Unit Nat := digitP

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

def radDigitPrefixP (radix : Radix) : Parsec Char String Unit String :=
  match radix with
  | .ten => pure $ ""
  | .sixteen => s.stringP "0x"

def radixP (radix : Radix) : Parsec Char String Unit Nat := do
  let _prefix ← radDigitPrefixP radix
  let digits ← someP $ radDigitP radix
  pure $ foldl (fun a x => radix * a + x) 0 digits

def decimalP : Parsec Char String Unit Nat := radixP .ten
def hexP : Parsec Char String Unit Nat := radixP .sixteen

def isHex? (x : String) : Bool :=
  parses? (s.lookAhead $ s.stringP "0x") x

def hod (x : String) : Radix :=
  if isHex? x then .sixteen else .ten

private def demoParse (φ : Parsec Char String Unit Nat) (x : String) : Either (ParseErrorBundle Char String Unit) Nat :=
  runParserP φ "" x

def ff y := do
  -- dbg_trace "."
  demoParse (radixP $ hod y) y

private def extractNat' (pr : Memo (ff x))
                        (doesParse : ∃ arg : Memo (ff x), Either.isRight arg.val)
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

structure Nat'' (x : String) :=
  parsed : Memo (ff x) := {}
  doesParse : (∃ arg : Memo (ff x), Either.isRight arg.val)
  val (arg : Memo (ff x)) : Nat := extractNat' arg doesParse

def isIdChar (x : Char) : Bool :=
  x.isAlphanum || "_.+-*/\\^~=<>!?@#$%&|:'`".data.elem x

def tt := ff "0xff"
#eval match tt with
| .left x => s!"{x}"
| .right y => s!"{y}"

def mtt : Memo (ff "23") := {}
#eval match mtt.val with
| .right x => s!"{x}"
| .left y => s!"{y}"

def proofMtt : ∃ arg : Memo (ff "23"), Either.isRight arg.val :=
  Exists.intro mtt $ match mttBranch : mtt.val with
  | .right y => by trivial
  | .left _ => by sorry

def ntt : Nat'' "23" := { doesParse := proofMtt }
#eval ntt.val ntt.parsed

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
