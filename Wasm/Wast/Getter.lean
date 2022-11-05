import Wasm.Wast.Num
import Wasm.Wast.Code
import Wasm.Wast.Name

open Cached
open Wasm.Wast.Name
open Wasm.Wast.Code.Type'

namespace Wasm.Wast.Getter

universe u
universe v

-- def f (t : Wasm.Wast.Code.Type'.Type') : Type :=
--   match t with
--   | .i _ => (x : String) → Wasm.Wast.Num.Num.Int.Int' x
--   | .f _ => (x : String) → Wasm.Wast.Num.Num.Float.Float' x
--   | .v _ => sorry

instance : CoeDep Type' (Type'.i 32) (String → Type) where
  coe := Wasm.Wast.Num.Num.Int.Int'

-- inductive Getter (α : Type') [CoeDep Type' α β] where
-- | const : β → Getter α
-- | local_i : Nat → Getter α
-- | local_n : (x : String → Option (Name x)) → Getter α
-- | stack : Getter α

inductive Getter (α : Type') (β : Type u) where
| const : (_ : β) → Getter α β
| local_i : Nat → Getter α β
| local_n : (x : String → Option (Name x)) → Getter α β
| stack : Getter α β

open Wasm.Wast.Num.Num.Int

def o_hundred : Option (Int' "23") := mkInt' "23"
def o_getter_hundred : Option $ Getter (Type'.i 32) (Int' "23") :=
  match o_hundred with
  | .some hundred => .some $ Getter.const hundred
  | .none => .none

def o_something (x : String) : Option (Int' x) := mkInt' x

/-

  (i32.const 0)

  between "(" ")"
    $ i32P


-/

def o_getter_i : Getter (Type'.i 32) ((x : String) → (Option $ Int' x)) :=
  Getter.const mkInt'

-- #check match o_hundred with
-- | .some hundred =>
--   Getter.const hundred
-- | .none => Getter.stack

end Wasm.Wast.Getter
