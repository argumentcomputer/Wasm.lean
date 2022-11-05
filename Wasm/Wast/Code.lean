import Megaparsec
import Megaparsec.Common
import Megaparsec.Errors.Bundle
import Megaparsec.Parsec
import Wasm.Wast.BitSize
import Wasm.Wast.Name

open Megaparsec
open Megaparsec.Common
open Megaparsec.Errors.Bundle
open Megaparsec.Parsec
open Wasm.Wast.Name

namespace Wasm.Wast.Code

namespace Type'

inductive Type' where
| f : BitSize → Type'
| i : BitSize → Type'
| v : BitSizeSIMD → Type'
    deriving BEq

instance : ToString Type' where
    toString x := match x with
    | .f y => "(Type'.f " ++ toString y ++ ")"
    | .i y => "(Type'.i " ++ toString y ++ ")"
    | .v y => "(Type'.v " ++ toString y ++ ")"

def typeP : Parsec Char String Unit Type' := do
    let ps ← getParserState
    let iorf ← (string "i" <|> string "f")
    let bits ← bitSizeP
    match iorf with
    | "i" => pure $ Type'.i bits
    | "f" => pure $ Type'.f bits
    | _ => parseError $ .trivial ps.offset .none [] -- Impossible, but it's easier to write and more performant.

end Type'

namespace Local

open Name
open Type'

structure LocalName where
    name : (x : String) → Option $ Name x

structure LocalIndex where
    index : Nat

inductive Local where
| name : LocalName → Local
| index : LocalIndex → Local

end Local

namespace Get

open Type'

inductive Get (x : Type') where
| from_stack
| by_name : LocalName → Get x
| by_index : LocalIndex → Get x
-- TODO: replace "Unit" placeholder with ConstFloat ⊕ ConstVec when implemented
| const : ConstInt ⊕ Unit → Get x

end Get

namespace Instruction

/- TODO: Instructions are rigid WAT objects. If we choose to only support
S-Expressions at this point, we don't need this concept. -/

end Instruction

namespace Operation

/- TODO: decide if we only support strict S-Exprs.
See here: https://zulip.yatima.io/#narrow/stream/20-meta/topic/WAST.20pair.20prog/near/30282 -/
structure Operation where

end Operation

namespace Func

open Name
open Type'
open Local
open Operation

structure Func where
    name : Option $ (x : String) → Option $ Name x
    export_ : Option String
    params : List Local
    result : Option Type'
    locals : List Local
    /- TODO -/
    ops : List Operation

end Func

namespace Module

/-

(module $target
    (func)
    (func $f (export "(module (func))") (param $y f32) (param $y1 f32) (result f32)
        (local $dummy i32)
        (i32.const 42)
        (local.set 2)
        (local.get $y1)
        (f32.add (local.get $y1))
        (local.get $y)
        (f32.add)
    )
    (func (export "main") (result f32)
        (local $x f32) (local $y f32)
        (local.set $x (f32.const 0.1))
        (local.set $y (f32.const 20.95))
        (call $f (local.get $x) (local.get $y))
    )
)

-/

open Name
open Type'
open Func

structure Module where
    name : Option $ (x : String) → Option $ Name x
    func : List Func

def moduleP : Parsec Char String Unit Module := sorry

end Module

namespace Block
end Block

namespace Loop
end Loop
