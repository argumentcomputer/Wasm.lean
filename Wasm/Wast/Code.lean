import Megaparsec
import Megaparsec.Common
import Megaparsec.Errors.Bundle
import Megaparsec.Parsec
import Wasm.Wast.BitSize
import Wasm.Wast.Name
import Wasm.Wast.Num
import Wasm.Wast.Parser.Common
import YatimaStdLib

open Megaparsec
open Megaparsec.Common
open Megaparsec.Errors.Bundle
open Megaparsec.Parsec
open MonadParsec
open Wasm.Wast.Name
open Wasm.Wast.Parser.Common
open Wasm.Wast.Num.Num.Int
open Wasm.Wast.Num.Num.Float

namespace Wasm.Wast.Code

namespace Type'

inductive Type' where
| f : BitSize → Type'
| i : BitSize → Type'
-- | v : BitSizeSIMD → Type'
    deriving BEq

instance : ToString Type' where
    toString x := match x with
    | .f y => "(Type'.f " ++ toString y ++ ")"
    | .i y => "(Type'.i " ++ toString y ++ ")"
    -- | .v y => "(Type'.v " ++ toString y ++ ")"

def typeP : Parsec Char String Unit Type' := do
    let ps ← getParserState
    let iorf ← (string "i" <|> string "f")
    let bits ← bitSizeP
    match iorf with
    | "i" => pure $ Type'.i bits
    | "f" => pure $ Type'.f bits
    | _ => @parseError (Parsec Char String Unit)
                        String String Unit Char
                        theInstance Type'
                        $ .trivial ps.offset .none $ hints0 Char

end Type'

namespace Local

open Name
open Type'

structure LocalName where
    name : String
    deriving BEq

instance : ToString LocalName where
    toString x := "(LocalName.mk " ++ x.name ++ ")"

structure LocalIndex where
    index : Nat
    deriving BEq

instance : ToString LocalIndex where
    toString x := "(LocalIndex.mk " ++ toString x.index ++ ")"

inductive Local where
| name : LocalName → Local
| index : LocalIndex → Local

end Local

namespace Get

open Type'
open Local

inductive Get (x : Type') where
| from_stack
| by_name : LocalName → Get x
| by_index : LocalIndex → Get x
-- TODO: replace "Unit" placeholder with ConstVec when implemented
-- TODO: generalise Consts the same way Get is generalised so that Get' i32 can't be populated with ConstFloat!
| const : (ConstInt ⊕ ConstFloat ⊕ Unit) → Get x

instance : ToString (Get α) where
    toString x := "(" ++ (
        match x with
        | .from_stack => "Get.from_stack"
        | .by_name n => "Get.by_name " ++ toString n
        | .by_index i => "Get.by_index " ++ toString i
        | .const ifu => "Get.const " ++ (match ifu with
            | .inl i => "(Sum.inl " ++ toString i ++ ")"
            | .inr $ .inl f => "(Sum.inr $ Sum.inl " ++ toString f ++ ")"
            | .inr $ .inr () => "(Sum.inr $ Sum.inr ())"
        )
    ) ++ " : Get " ++ toString α ++ ")"

def getConstP : Parsec Char String Unit (Get x) := do
    Seq.between (string "(") (string ")") do

        match x with
        | .i 32 => i32P >>= fun y => pure $ Get.const $ .inl y
        | .i 64 => i64P >>= fun y => pure $ Get.const $ .inl y
        | .f 32 => f32P >>= fun y => pure $ Get.const $ .inr $ .inl y
        | .f 64 => f64P >>= fun y => pure $ Get.const $ .inr $ .inl y

def getP : Parsec Char String Unit (Get x) := do
    -- TODO: implement locals!!!
    getConstP <|> (pure $ Get.from_stack)

end Get

namespace Instruction

/- TODO: Instructions are rigid WAT objects. If we choose to only support
S-Expressions at this point, we don't need this concept. -/

end Instruction

namespace Operation

/- TODO: decide if we only support strict S-Exprs.
See here: https://zulip.yatima.io/#narrow/stream/20-meta/topic/WAST.20pair.20prog/near/30282 -/
structure Operation where

open Type'
open Get

inductive Add' where
| f32 : Get (.f 32) → Get (.f 32) → Add'
| f64 : Get (.f 64) → Get (.f 64) → Add'
| i32 : Get (.i 32) → Get (.i 32) → Add'
| i64 : Get (.i 64) → Get (.i 64) → Add'

instance : ToString Add' where
    toString x := "(Add'." ++ match x with
    | .f32 u v => "f32 " ++ toString u ++ " " ++ toString v
    | .f64 u v => "f64 " ++ toString u ++ " " ++ toString v
    | .i32 u v => "i32 " ++ toString u ++ " " ++ toString v
    | .i64 u v => "i32 " ++ toString u ++ " " ++ toString v
    ++ ")"

def addP : Parsec Char String Unit Add' := do
    Seq.between (string "(") (string ")") do
        owP
        -- TODO: we'll use ps when we'll add more types into `Type'`.
        let _ps ← getParserState
        let add_t : Type' ←
            (string "i32.add" *> (pure $ .i 32) <|>
             string "i64.add" *> (pure $ .i 64) <|>
             string "f32.add" *> (pure $ .f 32) <|>
             string "f64.add" *> (pure $ .f 64))
        ignoreP
        let (arg_1 : Get add_t) ← getP
        owP
        let (arg_2 : Get add_t) ← getP
        owP
        match add_t with
        | .i 32 => pure $ Add'.i32 arg_1 arg_2
        | .i 64 => pure $ Add'.i64 arg_1 arg_2
        | .f 32 => pure $ Add'.f32 arg_1 arg_2
        | .f 64 => pure $ Add'.f64 arg_1 arg_2

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
