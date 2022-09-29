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

--------------------------------------------------
--               Type-level parsing             --
--------------------------------------------------

section cached

/-
Cached as a way to enforce that only the one correct value
is used. We use in in structures representing WAST types to
enforce correctness of inner values.
-/
private def Cached {α : Type u} (a : α) := { cached : α // cached = a }

instance : EmptyCollection (Cached a) where emptyCollection := ⟨a, rfl⟩
instance : Inhabited (Cached a) where default := {}
instance : Subsingleton (Cached a) where
  allEq := fun ⟨b, hb⟩ ⟨c, hc⟩ => by subst hb; subst hc; rfl
instance : DecidableEq (Cached a) := fun _ _ => isTrue (Subsingleton.allEq ..)
instance [Repr α] : Repr (Cached (a : α)) where
  reprPrec c n := reprPrec c.val n

end cached


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

private def extractNat' -- (x : String)
                  --  (pr : Either (ParseErrorBundle Char String Unit) Nat)-- := parse (parseRadixNat'Do $ hod x) x)
                   (pr : Either String Nat)-- := parse (parseRadixNat'Do $ hod x) x)
                   (doesParse : Either.isRight $ pr)
                   : Nat :=
  match pr with
  | .right y => y
  | .left _ => by
    unfold Either.isRight at doesParse
    simp at doesParse

private def parseRadixNat'Do' (_radix : Nat) (input : String) : Either String Nat :=
  if input == "23" then
    .right 100
  else if input == "55" then .right 55
  else
    .left "Menzoberranzan"

private def demoParse (φ : String → Either String Nat) (x : String) : Either String Nat :=
  φ x

def ff y := do
  dbg_trace "."
  demoParse (parseRadixNat'Do' $ hod y) y

structure Nat'' (x : String) :=
  -- valE : Cached (demoParse (parseRadixNat'Do' radix.val) x) := {}
  valE : Cached (ff x) := {}
  doesParse : Either.isRight valE.val := by simp
  val : Cached (extractNat' valE.val doesParse) := {}
  deriving DecidableEq, Repr

def nobug : Nat'' "23" := {}

-- @[simp] theorem eq_of_subsingleton [Subsingleton α] {a b : α} : (a = b) = True := by
--   simp [Subsingleton.allEq a b]

-- theorem extIff {a b : Nat'' x} : a = b ↔ x = x :=
--    ⟨fun h => by subst h; rfl, by cases a; cases b; intro h; cases h; simp⟩

def r : Cached (hod "23") := {}
def five : Cached (demoParse (parseRadixNat'Do' r.val) "23") := {}
theorem high_five : Either.isRight $ five.val := by simp
theorem noparse : Either.isRight $ demoParse (parseRadixNat'Do' (hod "23")) "23" := by simp
-- def bug : Nat'' "45" := { doesParse := noparse }


----------------------------
--          Name          --
----------------------------

def isIdChar (x : Char) : Bool :=
  x.isAlphanum || "_.+-*/\\^~=<>!?@#$%&|:'`".data.elem x

/- Captures a valid identifier.
-/
structure Name (x : String) where
  val : Cached x := {}
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
