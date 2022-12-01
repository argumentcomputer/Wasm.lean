import Wasm.Wast.Code
import Wasm.Wast.Num
import YatimaStdLib

open Wasm.Wast.Code
open Wasm.Wast.Code.Func
open Wasm.Wast.Code.Local
open Wasm.Wast.Code.Module
open Wasm.Wast.Code.Operation
open Wasm.Wast.Code.Type'
open Wasm.Wast.Num.Uni
open Cached

namespace Wasm.Engine

/- Likely unused hehe -/
-- structure Label where
--   frame : Int
--   kind : Byte --<-- this is an index of a 'continuation'

inductive EngineErrors where
| not_enough_stuff_on_stack
| param_type_incompatible
| local_with_given_name_missing : String → EngineErrors
| local_with_given_id_missing : Nat → EngineErrors
| function_not_found
| other -- JACKAL

instance : ToString EngineErrors where
  toString x := match x with
  | .not_enough_stuff_on_stack => "not enough stuff on stack"
  | .param_type_incompatible => "param type incompatible"
  | .local_with_given_id_missing i => s!"local #{i} not found"
  | .local_with_given_name_missing n => s!"local ``{n}'' not found"
  | .function_not_found => s!"function not found"
  | .other => "non-specified"

instance : Inhabited EngineErrors where
  default := .other

inductive StackEntry where
| num : NumUniT → StackEntry

/- TODO: I forgot what sort of other stacks are in standard lol, but ok. -/
structure Stack where
  es : List StackEntry

/- TODO: Functions for Stack? -/

/- TODO: This will eventually depend on ModuleInstance! -/
structure FunctionInstance (x : Module) where
  name : Option String
  export_ : Option String
  params : List Local
  result : List Type'
  locals : List Local -- These locals are indexed.
  index : Nat
  ops : List Operation


/- TODO: Unify this with Bytes.indexFuncs -/
def instantiateFs (m : Module) : List (FunctionInstance m) :=
  let go acc f :=
    let pl := reindexParamsAndLocals f
    let fi := FunctionInstance.mk f.name
                                  f.export_
                                  pl.1
                                  f.result
                                  pl.2
                                  0
                                  f.ops
    match acc with
    | [] => [fi]
    | x :: _ => {fi with index := x.index + 1} :: acc
  (m.func.foldl go []).reverse

structure Store (m : Module) where
  func : List (FunctionInstance m)

def mkStore (m : Module) : Store m :=
  Store.mk $ instantiateFs m

def funcByName (s : Store m) (x : String) : Option $ FunctionInstance m :=
  match s.func.filter (fun f => f.name == .some x) with
  | y :: [] => .some y
  | _ => .none

def fidByName (s : Store m) (x : String) : Option Nat :=
  funcByName s x >>= pure ∘ FunctionInstance.index

def paramTypecheck (x : Local) (y : StackEntry) :=
  let t := localToType x
  match y with
  | .num nn => match nn with
    | .i n => match t with
      | .i 32 => n.bs == 32
      | .i 64 => n.bs == 64
      | _ => false
    | .f n => match t with
      | .f 32 => n.bs == 32
      | .f 64 => n.bs == 64
      | _ => false

def findLocal (ls : List (Option String × Option StackEntry))
              (x : String)
              : Option StackEntry :=
  match ls.filter (fun se => .some x == se.1) with
  | y :: [] => y.2
  | _ => .none

mutual
  /- TODO: Support multi-output functions. -/
  partial def getSO (locals : List (Option String × Option StackEntry))
                    (stack : List StackEntry)
                    : Get' → Except EngineErrors (List StackEntry × StackEntry)
    | .from_stack => match stack with
      | [] => .error .not_enough_stuff_on_stack
      | s :: rest => .ok (rest, s)
    | .from_operation o => runOp locals stack o
    -- TODO: names are erased in production. See what do we want to do with this code path.
    | .by_name n => match findLocal locals n.name with
      | .none => .error $ .local_with_given_name_missing n.name
      | .some l => .ok (stack, l)
    | .by_index i => match locals.get? i.index with
      | .some (_, .some se)  => .ok (stack, se)
      | _ => .error $ .local_with_given_id_missing i.index
    | .i_const i => .ok $ (stack, .num $ NumUniT.i i)
    | .f_const f => .ok $ (stack, .num $ NumUniT.f f)

  -- TODO: there's a StateT somewhere here. Just sayin'
  partial def runOp (locals : List (Option String × Option StackEntry))
                    (stack : List StackEntry)
                    : Operation
                    → Except EngineErrors (List StackEntry × StackEntry)
    | .add add' => match add' with | .add _t g0 g1 => do
      let (stack', operand0) ← getSO locals stack g0
      let (stack1, operand1) ← getSO locals stack' g1
      let res ← match operand0, operand1 with
      | .num n0, .num n1 => match n0, n1 with
        | .i ⟨b0, i0⟩, .i ⟨_b1, i1⟩ => pure $ .num $ .i ⟨b0, i0 + i1⟩ -- TODO: check bitsize and overflow!
        | .f ⟨b0, f0⟩, .f ⟨_b1, f1⟩ => pure $ .num $ .f ⟨b0, f0 + f1⟩ -- check bitsize and overflow!
        | _, _ => throw .param_type_incompatible
      pure (res :: stack1, res)
end

def runDo (_s : Store m)
          (f : FunctionInstance m)
          (σ : Stack)
          : Except EngineErrors Stack := do
  let bite acc x :=
    match acc with
    | .error _ => acc
    | .ok cont => match cont.1.es with
      | [] => .error .not_enough_stuff_on_stack -- TODO: Better errors lol lol
      | y :: rest => if paramTypecheck x y then
        .ok (Stack.mk rest, y :: cont.2)
      else
        .error .param_type_incompatible
  let pσ ← f.params.foldl bite $ .ok (σ, [])
  let locals := (f.params ++ f.locals).map $
    fun l => match l with
      | .name ll => (.some ll.name, pσ.2.get? ll.index)
      | .index ll => (.none, pσ.2.get? ll.index)
  let go (oσ : Except EngineErrors Stack) (x : Operation)
         : Except EngineErrors Stack := do
    let stack ← oσ
    let naked_stack_and_result ← runOp locals (Stack.es stack) x
    pure $ Stack.mk naked_stack_and_result.1
  f.ops.foldl go $ .ok $ Stack.mk pσ.2

def run (s : Store m) (fid : Nat) (σ : Stack) : Except EngineErrors Stack :=
  match s.func.get? fid with
  | .none => .error .function_not_found
  | .some f => runDo s f σ
