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

structure Local where
    name : (x : String) → Option $ Name x
    type : Type'

end Local

namespace Func

open Name
open Type'

structure Func where
    name : (x : String) → Option $ Name x
    export_ : Option String
    params : List Local.Local
    result : Option Type'
    locals : List Local.Local


end Func

namespace Module

/-

(module $target
    (func)
    (func $f (export "(module (func))") (param $y f32) (param $y1 f32) (result f32)
        (local $dummy i32)
        i32.const 42
        (local.set 2)
        local.get $y1
        (f32.add (local.get $y1))
        local.get $y
        f32.add
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

structure Module where
    name : (x : String) → Option $ Name x
    func : List Func.Func

-- def moduleP : StateT Context (Parsec Char String Unit) Module := sorry
def moduleP : Parsec Char String Unit Module := sorry

end Module

namespace Block
end Block

namespace Loop
end Loop
