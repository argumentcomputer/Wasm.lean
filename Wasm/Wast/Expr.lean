/- WAST expressions as seen in the official test suite. -/

import Megaparsec.Char
import Megaparsec.Common
import Megaparsec.Errors.Bundle
import Megaparsec.String
import Megaparsec.Parsec

open Megaparsec.Char
open Megaparsec.Common
open Megaparsec.Errors.Bundle
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

/-

def isInr (x : PSum α β) : Prop :=
  match x with
  | .inr _ => True
  | .inl _ => False

theorem extrr (x : PSum α β) (hE : ∃ y : β, x = .inr y) : isInr x :=
  Exists.elim hE
    (fun _ =>
      fun xeq =>
        xeq ▸ trivial
    )

theorem extrr1 (x : PSum α β) (hI : isInr x) : ∃ y : β, x = .inr y :=
  match x with
  | .inr yy =>
    Exists.intro yy rfl
  | .inl _ =>
    False.elim hI

theorem extrr2 (x : PSum α β) : (isInr x) ↔ (∃ y : β, x = .inr y) :=
  Iff.intro
    (extrr1 x)
    (extrr x)

-/

private def parseDigit (p : Char → Bool) : Parsec Char String Unit (List Nat × Nat × Nat) := do
   let accradmul ← s.getParserState
   let y ← c.satisfy p
  --  let a := c2ia y accradmul
   sorry

private def parseRadixNat'Do (radix : Nat)
                            --  : Parsec Char String Unit (List Nat × Nat × Nat) :=
                             : Parsec Char String Unit Nat := do
  let _x ← s.stringP "23"
  pure 100

def isHex? (x : String) : Bool :=
  parses? (s.lookAhead $ s.stringP "0x") x

def hod (x : String) : Nat :=
  if isHex? x then 16 else 10

inductive Exp
  | var (i : Nat)
  | app (a b : Exp)
with
  @[computedField] hash : Exp → Nat
    | .var i => i
    | .app a b => a.hash * b.hash + 1

structure Memo {α : Type u} (a : α) :=
  val : α
  proof : val = a

instance : EmptyCollection (Memo a) where emptyCollection := ⟨a, rfl⟩
instance : Inhabited (Memo a) where default := {}
instance : Subsingleton (Memo a) where
  allEq := fun ⟨b, hb⟩ ⟨c, hc⟩ => by subst hb; subst hc; rfl
instance : DecidableEq (Memo a) := fun _ _ => isTrue (Subsingleton.allEq ..)

private def parseRadixNat'Do' (_radix : Nat) (input : String) : Either String Nat :=
  if input == "23" then
    .right 100
  else if input == "55" then
    .right 55
  else
    .left "Menzoberranzan"

private def demoParse (φ : String → Either String Nat) (x : String) : Either String Nat :=
  φ x

def ff y := do
  dbg_trace "."
  demoParse (parseRadixNat'Do' $ hod y) y

private def extractNat' (pr : Memo (ff x))-- := parse (parseRadixNat'Do $ hod x) x)
                        (doesParse : ∃ arg : Memo (ff x), Either.isRight arg.val)
                        -- (doesParse : ∃ arg : Memo (ff x), isR arg.val)
                        : Nat :=
  match h : pr.val with
  | .right y => y
  | .left _ => by
      have : False :=
        Exists.elim doesParse (fun earg =>
          fun isRightHypothesis => by
            -- have : earg = pr := Subsingleton.elim earg pr
            -- rw [this, h] at isRightHypothesis
            -- unfold Either.isRight at isRightHypothesis
            simp only [Subsingleton.elim earg pr, h, Either.isRight] at isRightHypothesis
          )
      contradiction

structure Nat'' (x : String) :=
  parsed : Memo (ff x) := {}
  doesParse : (∃ arg : Memo (ff x), Either.isRight arg.val)
  val (arg : Memo (ff x)) : Nat := extractNat' arg doesParse

def five : Memo (ff "23") := {}
def seven : Memo (ff "55") := {}
-- theorem high_five : fun _ => Either.isRight $ five.val := by
--   simp
-- def high_five (arg : Memo (ff "23")) : Either.isRight arg.val := by sorry
  -- match arg.val with
  -- | .right y => trivial
  -- | .left a => ???

-- def bug : Nat'' "23" :=
--   { doesParse := high_five }
-- #check bug
-- #eval bug.val five
-- #eval bug.val seven

def demo : Nat'' "23" := {
  doesParse := Exists.intro five $ by
    trivial
}

#eval demo.val demo.parsed

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
