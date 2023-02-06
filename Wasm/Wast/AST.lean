import Wasm.Wast.BitSize
import Wasm.Wast.Num

open Wasm.Wast.Num.Num.Int
open Wasm.Wast.Num.Num.Float
open Wasm.Wast.Num.Uni

namespace Wasm.Wast.AST
section AST


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

def numUniType : NumUniT → Type'
  | .i x => .i x.bs
  | .f x => .f x.bs

def bitsize : Type' → BitSize
  | .f bs => bs
  | .i bs => bs

end Type'
open Type'

namespace Local

structure Local where
  index : Nat
  name : Option String
  type : Type' -- TODO: We need to pack lists with different related types'. For that we need something cooler than List, but since we're just coding now, we'll do it later.
  deriving BEq

instance : ToString Local where
  toString x := s!"(Local.mk {x.index} {x.type})"

end Local
open Local

namespace LabelIndex

structure LabelIndex where
  li : Nat
  deriving Repr, DecidableEq

instance : Coe Nat LabelIndex where
  coe n := ⟨n⟩

instance : Coe LabelIndex Nat where
  coe | ⟨n⟩ => n

instance : ToString LabelIndex where
  toString | ⟨n⟩ => s!"(LabelIndex {n})"

end LabelIndex
open LabelIndex


/- TODO: Instructions are rigid WAT objects. If we choose to only support
S-Expressions at this point, we don't need this concept. -/
namespace Instruction
end Instruction


namespace Operation

mutual
  -- Sadge
  inductive Get' where
  | from_stack
  | from_operation : Operation → Get'
  | by_name : Local → Get'
  | by_index : Local → Get'

-- TODO: add support for function type indexes for blocktypes
-- TODO: branching ops can produce and consume operands themselves,
-- e.g. `(br 0 (i32.const 2))`. Right now we don't support it, but should we?
-- TODO: replace `NumUniT` with something supporting `ConstVec` when implemented
-- TODO: generalise Consts the same way Get is generalised so that `i32.const`
-- can't be populated with `ConstFloat`!
  inductive Operation where
  | nop
  | drop
  | const : Type' → NumUniT → Operation
  | eqz : Type' → Get' → Operation
  | eq  : Type' → Get' → Get' → Operation
  | ne  : Type' → Get' → Get' → Operation
  | lt_u  : Type' → Get' → Get' → Operation
  | lt_s  : Type' → Get' → Get' → Operation
  | gt_u  : Type' → Get' → Get' → Operation
  | gt_s  : Type' → Get' → Get' → Operation
  | le_u  : Type' → Get' → Get' → Operation
  | le_s  : Type' → Get' → Get' → Operation
  | ge_u  : Type' → Get' → Get' → Operation
  | ge_s  : Type' → Get' → Get' → Operation
  | lt  : Type' → Get' → Get' → Operation
  | gt  : Type' → Get' → Get' → Operation
  | le  : Type' → Get' → Get' → Operation
  | ge  : Type' → Get' → Get' → Operation
  | clz : Type' → Get' → Operation
  | ctz : Type' → Get' → Operation
  | popcnt : Type' → Get' → Operation
  | add : Type' → Get' → Get' → Operation
  | sub : Type' → Get' → Get' → Operation
  | mul : Type' → Get' → Get' → Operation
  | div : Type' → Get' → Get' → Operation
  | max : Type' → Get' → Get' → Operation
  | min : Type' → Get' → Get' → Operation
  | div_s : Type' → Get' → Get' → Operation
  | div_u : Type' → Get' → Get' → Operation
  | rem_s : Type' → Get' → Get' → Operation
  | rem_u : Type' → Get' → Get' → Operation
  | and : Type' → Get' → Get' → Operation
  | or : Type' → Get' → Get' → Operation
  | xor : Type' → Get' → Get' → Operation
  | shl : Type' → Get' → Get' → Operation
  | shr_u : Type' → Get' → Get' → Operation
  | shr_s : Type' → Get' → Get' → Operation
  | rotl : Type' → Get' → Get' → Operation
  | rotr : Type' → Get' → Get' → Operation
  | block : List Type' → List Operation → Operation
  | loop : List Type' → List Operation → Operation
  | if : List Type' → List Operation → List Operation → Operation
  | br : LabelIndex → Operation
  | br_if : LabelIndex → Operation
end

mutual
  private partial def getToString (x : Get') : String :=
    "(Get'" ++ (
      match x with
      | .from_stack => ".from_stack"
      | .from_operation o => s!".from_operation {operationToString o}"
      | .by_name n => ".by_name " ++ toString n
      | .by_index i => ".by_index " ++ toString i
    ) ++ ")"

  private partial def operationToString : Operation → String
    | .nop => "(Operation.nop)"
    | .drop => "(Operation.drop)"
    | .const t n => s!"(Operation.const {t} {n})"
    | .eqz t g => s!"(Operation.eqz {t} {getToString g})"
    | .eq  t g1 g2 => s!"(Operation.eq {t} {getToString g1} {getToString g2})"
    | .ne  t g1 g2 => s!"(Operation.ne {t} {getToString g1} {getToString g2})"
    | .lt_u t g1 g2 =>
      s!"(Operation.lt_u {t} {getToString g1} {getToString g2})"
    | .lt_s t g1 g2 =>
      s!"(Operation.lt_s {t} {getToString g1} {getToString g2})"
    | .gt_u t g1 g2 =>
      s!"(Operation.gt_u {t} {getToString g1} {getToString g2})"
    | .gt_s t g1 g2 =>
      s!"(Operation.gt_s {t} {getToString g1} {getToString g2})"
    | .le_u t g1 g2 =>
      s!"(Operation.le_u {t} {getToString g1} {getToString g2})"
    | .le_s t g1 g2 =>
      s!"(Operation.le_s {t} {getToString g1} {getToString g2})"
    | .ge_u t g1 g2 =>
      s!"(Operation.ge_u {t} {getToString g1} {getToString g2})"
    | .ge_s t g1 g2 =>
      s!"(Operation.ge_s {t} {getToString g1} {getToString g2})"
    | .lt  t g1 g2 => s!"(Operation.lt {t} {getToString g1} {getToString g2})"
    | .gt  t g1 g2 => s!"(Operation.gt {t} {getToString g1} {getToString g2})"
    | .le  t g1 g2 => s!"(Operation.le {t} {getToString g1} {getToString g2})"
    | .ge  t g1 g2 => s!"(Operation.ge {t} {getToString g1} {getToString g2})"
    | .clz t g => s!"(Operation.clz {t} {getToString g})"
    | .ctz t g => s!"(Operation.ctz {t} {getToString g})"
    | .popcnt t g => s!"(Operation.popcnt {t} {getToString g})"
    | .add t g1 g2 => s!"(Operation.add {t} {getToString g1} {getToString g2})"
    | .sub t g1 g2 => s!"(Operation.sub {t} {getToString g1} {getToString g2})"
    | .mul t g1 g2 => s!"(Operation.mul {t} {getToString g1} {getToString g2})"
    | .div t g1 g2 => s!"(Operation.div {t} {getToString g1} {getToString g2})"
    | .max t g1 g2 => s!"(Operation.max {t} {getToString g1} {getToString g2})"
    | .min t g1 g2 => s!"(Operation.min {t} {getToString g1} {getToString g2})"
    | .div_s t g1 g2 =>
      s!"(Operation.div_s {t} {getToString g1} {getToString g2})"
    | .div_u t g1 g2 =>
      s!"(Operation.div_u {t} {getToString g1} {getToString g2})"
    | .rem_s t g1 g2 =>
      s!"(Operation.rem_s {t} {getToString g1} {getToString g2})"
    | .rem_u t g1 g2 =>
      s!"(Operation.rem_u {t} {getToString g1} {getToString g2})"
    | .and t g1 g2 => s!"(Operation.and {t} {getToString g1} {getToString g2})"
    | .or t g1 g2 => s!"(Operation.or {t} {getToString g1} {getToString g2})"
    | .xor t g1 g2 => s!"(Operation.xor {t} {getToString g1} {getToString g2})"
    | .shl t g1 g2 => s!"(Operation.shl {t} {getToString g1} {getToString g2})"
    | .shr_u t g1 g2 =>
      s!"(Operation.shr_u {t} {getToString g1} {getToString g2})"
    | .shr_s t g1 g2 =>
      s!"(Operation.shr_s {t} {getToString g1} {getToString g2})"
    | .rotl t g1 g2 =>
      s!"(Operation.rotl {t} {getToString g1} {getToString g2})"
    | .rotr t g1 g2 =>
      s!"(Operation.rotr {t} {getToString g1} {getToString g2})"
    | .block ts is => s!"(Operation.block {ts} {is.map operationToString})"
    | .loop ts is => s!"(Operation.loop {ts} {is.map operationToString})"
    | .if ts thens elses => s!"(Operation.if {ts} {thens.map operationToString} {elses.map operationToString})"
    | .br li => s!"(Operation.br {li})"
    | .br_if li => s!"(Operation.br_if {li})"

end

instance : ToString Get' where
  toString := getToString

instance : ToString Operation where
  toString := operationToString

end Operation
open Operation


namespace Func

structure Func where
  name : Option String
  export_ : Option String
  -- TODO: Heterogenous lists so that we can promote Type'?
  params : List Local
  results : List Type'
  locals : List Local
  ops : List Operation

instance : ToString Func where
  toString x := s!"(Func.mk {x.name} {x.export_} {x.params} {x.results} {x.locals} {x.ops})"

end Func
open Func


namespace Module

structure Module where
  name : Option String
  func : List Func

instance : ToString Module where
  toString x := s!"(Module.mk {x.name} {x.func})"

end Module


end AST
end Wasm.Wast.AST
