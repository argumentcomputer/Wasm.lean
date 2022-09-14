/- WAST expressions as seen in the official test suite. -/

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

/- Opaque structure that captures a particular string at type level.

TODO make it actually opaque: https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Export.20smart.20constructor.20but.20also.20the.20type/near/298828483 -/
structure Name (x : String) where
  val : String := x
  deriving Repr

def isIdChar (x : Char) : Bool :=
  x.isAlphanum || "_.+-*/\\^~=<>!?@#$%&|:'`".data.elem x

def mkName (xs : String) : Option (Name xs) :=
  let xs' := xs.data
  if xs'.length == 0 then
    .none
  else
    if List.foldl (fun a x => if a then isIdChar x else false) true xs.data then
      .some {}
    else
      .none

#eval (5 : Nat) + BitSize.thirtyTwo
#eval 5 + (BitSize.sixtyFour : Nat)
#eval (Ord.compare BitSize.sixtyFour BitSize.thirtyTwo) == Ordering.gt

def hello : Name "hello" := {}

#eval hello.val

-- wrap : n m | n > m
-- extend : n m | n < m