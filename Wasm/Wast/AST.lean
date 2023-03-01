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
  deriving DecidableEq

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
  name : Option String
  type : Type' -- TODO: We need to pack lists with different related types'. For that we need something cooler than List, but since we're just coding now, we'll do it later.
  deriving DecidableEq

instance : ToString Local where
  toString
    | ⟨.some name, t⟩ => s!"(Local.mk \"{name}\" {t})"
    | ⟨.none,      t⟩ => s!"(Local.mk {t})"

inductive LocalLabel where
  | by_index : Nat → LocalLabel
  | by_name : String → LocalLabel
  deriving Repr, DecidableEq

instance : ToString LocalLabel where
  toString | .by_index n => s!"(LocalLabel.by_index {n})"
           | .by_name  n => s!"(LocalLabel.by_name \"{n}\")"

end Local
open Local

namespace Global

inductive GlobalLabel where
  | by_index : Nat → GlobalLabel
  | by_name : String → GlobalLabel
  deriving Repr, DecidableEq

instance : ToString GlobalLabel where
  toString | .by_index n => s!"(GlobalLabel.by_index {n})"
           | .by_name  n => s!"(GlobalLabel.by_name \"{n}\")"

end Global
open Global

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

-- TODO: add support for function type indexes for blocktypes
-- TODO: branching ops can produce and consume operands themselves,
-- e.g. `(br 0 (i32.const 2))`. Right now we don't support it, but should we?
-- TODO: replace `NumUniT` with something supporting `ConstVec` when implemented
-- TODO: generalise Consts the same way Get is generalised so that `i32.const`
-- can't be populated with `ConstFloat`!
  inductive Operation where
  | nop
  --------------------- PARAMETRIC ----------------------
  | drop
  ----------------------  NUMERIC -----------------------
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
  ---------------------- VARIABLE -----------------------
  | local_get : LocalLabel → Operation
  | local_set : LocalLabel → Operation
  | local_tee : LocalLabel → Operation
  | global_get : GlobalLabel → Operation
  | global_set : GlobalLabel → Operation
  ----------------------- CONTROL -----------------------
  | block : List Type' → List Operation → Operation
  | loop : List Type' → List Operation → Operation
  | if : List Type' → Get' → List Operation → List Operation → Operation
  | br : LabelIndex → Operation
  | br_if : LabelIndex → Operation
end

mutual
  private partial def getToString : Get' → String
    | .from_stack => "(Get'.from_stack)"
    | .from_operation o => s!"(Get'.from_operation {operationToString o})"

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
    | .local_get l => s!"(Operation.local_get {l})"
    | .local_set l => s!"(Operation.local_set {l})"
    | .local_tee l => s!"(Operation.local_tee {l})"
    | .global_get l => s!"(Operation.global_get {l})"
    | .global_set l => s!"(Operation.global_set {l})"
    | .block ts is => s!"(Operation.block {ts} {is.map operationToString})"
    | .loop ts is => s!"(Operation.loop {ts} {is.map operationToString})"
    | .if ts g thens elses => s!"(Operation.if {ts} {getToString g} {thens.map operationToString} {elses.map operationToString})"
    | .br li => s!"(Operation.br {li})"
    | .br_if li => s!"(Operation.br_if {li})"

end

instance : ToString Get' where
  toString := getToString

instance : ToString Operation where
  toString := operationToString

end Operation
open Operation


namespace Global

structure GlobalType where
  mut? : Bool
  type : Type'
  deriving DecidableEq

instance : ToString GlobalType where
  toString
    | ⟨false, t⟩ => s!"(GlobalType const {t})"
    | ⟨true,  t⟩ => s!"(GlobalType var {t})"

structure Global where
  name : Option String
  type : GlobalType
  init : Operation

instance : ToString Global where
  toString
    | ⟨.some name, type, init⟩ => s!"(Global \"{name}\" {type} {init})"
    | ⟨.none,      type, init⟩ => s!"(Global {type} {init})"

end Global
open Global

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
  globals : List Global
  func : List Func

instance : ToString Module where
  toString x := s!"(Module.mk {x.name} {x.globals} {x.func})"

end Module


end AST
end Wasm.Wast.AST
