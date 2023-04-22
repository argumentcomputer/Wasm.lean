import Wasm.Wast.BitSize
import Wasm.Wast.Num

open Wasm.Wast.Num.Num.Int
open Wasm.Wast.Num.Uni

namespace Wasm.Wast.AST
section AST


inductive Type' where
  | i : BitSize → Type'
  -- | v : BitSizeSIMD → Type'
  deriving DecidableEq

namespace Type'

instance : ToString Type' where
  toString x := match x with
  | .i y => "(Type'.i " ++ toString y ++ ")"
  -- | .v y => "(Type'.v " ++ toString y ++ ")"

def numUniType : NumUniT → Type'
  | .i x => .i x.bs

def bitsize : Type' → BitSize
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

namespace BlockLabel

inductive BlockLabelId where
  | by_index : Nat → BlockLabelId
  | by_name : String → BlockLabelId
  deriving Repr, DecidableEq

instance : Coe Nat BlockLabelId where
  coe n := .by_index n

instance : ToString BlockLabelId where
  toString | .by_index n => s!"(BlockLabelId.by_index {n})"
           | .by_name ln => s!"(BlockLabelId.by_name {ln})"

end BlockLabel
open BlockLabel

namespace FuncLabel

inductive FuncId where
  | by_index : Nat → FuncId
  | by_name : String → FuncId
  deriving Repr, DecidableEq

instance : Coe Nat FuncId where
  coe n := .by_index n

instance : ToString FuncId where
  toString | .by_index n => s!"(FuncId.by_index {n})"
           | .by_name ln => s!"(FuncId.by_name {ln})"

end FuncLabel
open FuncLabel

structure FunctionType where
  tid : Option String
  ins  : List Local
  outs : List Type'
  deriving DecidableEq, Inhabited

namespace FunctionType

instance : ToString FunctionType where
  toString x := s!"(FunctionType {x.ins} {x.outs})"

def mkFunctionType (param : List Local) (results : List Type') : FunctionType :=
  ⟨.none, param, results⟩

inductive FTypeId where
  | by_index : Nat → FTypeId
  | by_name : String → FTypeId
  deriving Repr, DecidableEq

instance : Coe Nat FTypeId where
  coe n := .by_index n

instance : ToString FTypeId where
  toString | .by_index n => s!"(FTypeId.by_index {n})"
           | .by_name ln => s!"(FTypeId.by_name {ln})"


end FunctionType
open FunctionType

/- TODO: Instructions are rigid WAT objects. If we choose to only support
S-Expressions at this point, we don't need this concept. -/
namespace Instruction
end Instruction


namespace Operation

-- TODO: add support for function type indexes for blocktypes
-- TODO: branching ops can produce and consume operands themselves,
-- e.g. `(br 0 (i32.const 2))`. Right now we don't support it, but should we?
-- TODO: replace `NumUniT` with something supporting `ConstVec` when implemented
-- TODO: generalise Consts the same way Get is generalised so that `i32.const`
-- can't be populated with `ConstFloat`!
inductive Operation where
| unreachable
| nop
--------------------- PARAMETRIC ----------------------
| drop
| select : Option Type' → Operation
----------------------  NUMERIC -----------------------
| const : Type' → NumUniT → Operation
| eqz : Type' → Operation
| eq  : Type' → Operation
| ne  : Type' → Operation
| lt_u  : Type' → Operation
| lt_s  : Type' → Operation
| gt_u  : Type' → Operation
| gt_s  : Type' → Operation
| le_u  : Type' → Operation
| le_s  : Type' → Operation
| ge_u  : Type' → Operation
| ge_s  : Type' → Operation
| lt  : Type' → Operation
| gt  : Type' → Operation
| le  : Type' → Operation
| ge  : Type' → Operation
| clz : Type' → Operation
| ctz : Type' → Operation
| popcnt : Type' → Operation
| add : Type' → Operation
| sub : Type' → Operation
| mul : Type' → Operation
| div : Type' → Operation
| max : Type' → Operation
| min : Type' → Operation
| div_s : Type' → Operation
| div_u : Type' → Operation
| rem_s : Type' → Operation
| rem_u : Type' → Operation
| and : Type' → Operation
| or : Type' → Operation
| xor : Type' → Operation
| shl : Type' → Operation
| shr_u : Type' → Operation
| shr_s : Type' → Operation
| rotl : Type' → Operation
| rotr : Type' → Operation
---------------------- VARIABLE -----------------------
| local_get : LocalLabel → Operation
| local_set : LocalLabel → Operation
| local_tee : LocalLabel → Operation
| global_get : GlobalLabel → Operation
| global_set : GlobalLabel → Operation
----------------------- CONTROL -----------------------
| block : Option String → List Local → List Type' → List Operation → Operation
| loop : Option String → List Local → List Type' → List Operation → Operation
| if : Option String → List Local → List Type'
          → List Operation → List Operation → Operation
| br : BlockLabelId → Operation
| br_if : BlockLabelId → Operation
| br_table : List BlockLabelId → BlockLabelId → Operation
| call : FuncId → Operation
| return : Operation

private partial def operationToString : Operation → String
  | .unreachable => "(Operation.unreachable)"
  | .nop => "(Operation.nop)"
  | .drop => "(Operation.drop)"
  | .select t => s!"(Operation.select {t})"
  | .const t n => s!"(Operation.const {t} {n})"
  | .eqz t => s!"(Operation.eqz {t})"
  | .eq  t => s!"(Operation.eq {t})"
  | .ne  t => s!"(Operation.ne {t})"
  | .lt_u t => s!"(Operation.lt_u {t})"
  | .lt_s t => s!"(Operation.lt_s {t})"
  | .gt_u t => s!"(Operation.gt_u {t})"
  | .gt_s t => s!"(Operation.gt_s {t})"
  | .le_u t => s!"(Operation.le_u {t})"
  | .le_s t => s!"(Operation.le_s {t})"
  | .ge_u t => s!"(Operation.ge_u {t})"
  | .ge_s t => s!"(Operation.ge_s {t})"
  | .lt  t => s!"(Operation.lt {t})"
  | .gt  t => s!"(Operation.gt {t})"
  | .le  t => s!"(Operation.le {t})"
  | .ge  t => s!"(Operation.ge {t})"
  | .clz t => s!"(Operation.clz {t})"
  | .ctz t => s!"(Operation.ctz {t})"
  | .popcnt t => s!"(Operation.popcnt {t})"
  | .add t => s!"(Operation.add {t})"
  | .sub t => s!"(Operation.sub {t})"
  | .mul t => s!"(Operation.mul {t})"
  | .div t => s!"(Operation.div {t})"
  | .max t => s!"(Operation.max {t})"
  | .min t => s!"(Operation.min {t})"
  | .div_s t => s!"(Operation.div_s {t})"
  | .div_u t => s!"(Operation.div_u {t})"
  | .rem_s t => s!"(Operation.rem_s {t})"
  | .rem_u t => s!"(Operation.rem_u {t})"
  | .and t => s!"(Operation.and {t})"
  | .or t => s!"(Operation.or {t})"
  | .xor t => s!"(Operation.xor {t})"
  | .shl t => s!"(Operation.shl {t})"
  | .shr_u t => s!"(Operation.shr_u {t})"
  | .shr_s t => s!"(Operation.shr_s {t})"
  | .rotl t => s!"(Operation.rotl {t})"
  | .rotr t => s!"(Operation.rotr {t})"
  | .local_get l => s!"(Operation.local_get {l})"
  | .local_set l => s!"(Operation.local_set {l})"
  | .local_tee l => s!"(Operation.local_tee {l})"
  | .global_get l => s!"(Operation.global_get {l})"
  | .global_set l => s!"(Operation.global_set {l})"
  | .block id pts rts is =>
    s!"(Operation.block {id} {pts} {rts} {is.map operationToString})"
  | .loop id pts rts is =>
    s!"(Operation.loop {id} {pts} {rts} {is.map operationToString})"
  | .if id pts rts thens elses =>
    s!"(Operation.if {id} {pts} {rts} {thens.map operationToString} {elses.map operationToString})"
  | .br sl => s!"(Operation.br {sl})"
  | .br_if sl => s!"(Operation.br_if {sl})"
  | .br_table sls sdef => s!"(Operation.br_table {sls} {sdef})"
  | .call fi => s!"(Operation.call {fi})"
  | .return => s!"(Operation.return)"

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

namespace BlockLabel

structure BlockLabel where
  name : Option String
  arity : Nat
  ops : List Operation

instance : ToString BlockLabel where
  toString x := s!"(Label.mk {x.name} {x.arity} {x.ops})"

end BlockLabel

structure Func where
  name : Option String
  export_ : Option String
  ftype : Sum FTypeId (List Local × List Type')
  locals : List Local
  ops : List Operation

namespace Func

instance : ToString Func where
  toString x :=
    match x.ftype with
    | .inl tid => s!"(Func.mk {x.name} {x.export_} {tid} {x.locals} {x.ops})"
    | .inr (params, results) => s!"(Func.mk {x.name} {x.export_} {params} {results} {x.locals} {x.ops})"

end Func
open Func


namespace Module

structure Module where
  name : Option String
  types : List FunctionType
  globals : List Global
  func : List Func

instance : ToString Module where
  toString x := s!"(Module.mk {x.name} {x.types} {x.globals} {x.func})"

end Module


end AST
end Wasm.Wast.AST
