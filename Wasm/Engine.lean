import Wasm.Wast.AST
import Wasm.Wast.Code
import Wasm.Wast.Num
import YatimaStdLib

open Wasm.Wast.AST
open Wasm.Wast.AST.Func
open Wasm.Wast.AST.LabelIndex
open Wasm.Wast.AST.Local
open Wasm.Wast.AST.Module
open Wasm.Wast.AST.Operation
open Wasm.Wast.AST.Type'
open Wasm.Wast.Code
open Wasm.Wast.Num.Uni
open Cached

namespace Wasm.Engine

inductive EngineErrors where
| not_enough_stuff_on_stack
| stack_incompatible_with_results
| param_type_incompatible
| typecheck_failed
| local_with_no_name_given
| local_with_given_name_missing : String → EngineErrors
| local_with_given_id_missing : Nat → EngineErrors
| function_not_found
| other -- JACKAL

instance : ToString EngineErrors where
  toString x := match x with
  | .not_enough_stuff_on_stack => "not enough stuff on stack"
  | .stack_incompatible_with_results => "stack incompatible with result types"
  | .param_type_incompatible => "param type incompatible"
  | .typecheck_failed => s!"typecheck failed"
  | .local_with_no_name_given => s!"local with no name given"
  | .local_with_given_id_missing i => s!"local #{i} not found"
  | .local_with_given_name_missing n => s!"local ``{n}'' not found"
  | .function_not_found => s!"function not found"
  | .other => "non-specified"

instance : Inhabited EngineErrors where
  default := .other

/- Likely unused hehe <---- I WISH -/
structure Label where
  arity : Nat
  ops : List Operation

instance : ToString Label where
  toString x := s!"(Label.mk {x.arity} {x.ops})"

namespace StackEntry

inductive StackEntry where
| num : NumUniT → StackEntry
| label : Label → StackEntry

instance : ToString StackEntry where
  toString | .num n => s!"(StackEntry.num {n})"
           | .label l => s!"(StackEntry.label {l})"

def isLabel : StackEntry → Bool
  | .num _ => false
  | .label _ => true

def isValue : StackEntry → Bool
  | .num _ => true
  | .label _ => false

end StackEntry
open StackEntry

/- TODO: I forgot what sort of other stacks are in standard lol, but ok. -/
structure Stack where
  es : List StackEntry

instance : ToString Stack where
  toString | ⟨es⟩ => s!"(Stack {es})"

def stackValues (stack : Stack) : List StackEntry :=
  stack.es.filter isValue

def stackLabels (stack : Stack) : List StackEntry :=
  stack.es.filter isLabel

def skimValues (stack : Stack) : List StackEntry :=
  stack.es.dropWhile isValue

def fetchLabel (stack : Stack) (idx : LabelIndex) : Option Label :=
  let rec go
    | [], _ => .none
    | .label l :: _, 0 => .some l
    | .num _ :: es, n => go es n
    | .label _ :: es, n+1 => go es n
  go stack.es idx.li

/- TODO: This will eventually depend on ModuleInstance! -/
structure FunctionInstance (x : Module) where
  name : Option String
  export_ : Option String
  params : List Local
  results : List Type'
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
                                  f.results
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
  match s.func.filter (fun f => f.export_ == .some x) with
  | y :: [] => .some y
  | _ => .none

def fidByName (s : Store m) (x : String) : Option Nat :=
  funcByName s x >>= pure ∘ FunctionInstance.index

def stackEntryTypecheck (x : Type') (y : StackEntry) :=
  match y with
  | .num nn => match nn with
    | .i n => match x with
      | .i 32 => n.bs == 32
      | .i 64 => n.bs == 64
      | _ => false
    | .f n => match x with
      | .f 32 => n.bs == 32
      | .f 64 => n.bs == 64
      | _ => false
  | .label _ => false

-- Checks that the given numerical values correspond to the given
-- types both in the type of each respective value and in length.
def resultsTypecheck : List Type' → List StackEntry → Bool
  | [], [] => true
  | t :: ts, e :: es =>
    if stackEntryTypecheck t e then resultsTypecheck ts es else false
  | _, _ => false

def findLocalByName? (ls : List (Option String × Option StackEntry))
                    (x : String) : Option StackEntry :=
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
    | .from_operation o => do
      -- Some instructions do not produce a value/do not change stack.
      let stack' ← runOp locals stack o
      match stack' with
      | [] => .error .not_enough_stuff_on_stack
      | s :: rest => .ok (rest, s)
    -- TODO: names are erased in production. See what do we want to do with this code path.
    | .by_name n => match n.name with
      | .none => .error .local_with_no_name_given
      | .some name => match findLocalByName? locals name with
        | .none => .error $ .local_with_given_name_missing name
        | .some l => .ok (stack, l)
    | .by_index i => match locals.get? i.index with
      | .some (_, .some se)  => .ok (stack, se)
      | _ => .error $ .local_with_given_id_missing i.index

  -- TODO: there's a StateT somewhere here. Just sayin'
  -- TODO: we're not typechecking at all!
  -- TODO: can locals change when executing nested instructions?
  partial def runOp (locals : List (Option String × Option StackEntry))
                    (stack : List StackEntry)
                    : Operation
                    → Except EngineErrors (List StackEntry)
    | .nop => pure stack
    | .const _t n => pure $ .num n :: stack
    | .add _t g0 g1 => do
      let (stack', operand0) ← getSO locals stack g0
      let (stack1, operand1) ← getSO locals stack' g1
      let res ← match operand0, operand1 with
        | .num (.i ⟨b0, i0⟩), .num (.i ⟨_b1, i1⟩) => pure $ .num $ .i ⟨b0, i0 + i1⟩ -- TODO: check bitsize and overflow!
        | .num (.f ⟨b0, f0⟩), .num (.f ⟨_b1, f1⟩) => pure $ .num $ .f ⟨b0, f0 + f1⟩ -- TODO: check bitsize and overflow!
        | _, _ => throw .param_type_incompatible
      pure (res :: stack1)
    | .block ts ops => do
      -- TODO: currently, we only support simple [] → [valuetype*] blocks,
      -- not type indices. For this reason, we start the block execution
      -- with an stack devoid of _values_ to simulate 0-input-arity, but we
      -- still pass in all the labels currently reachable.
      let innerStack := .label ⟨ts.length, []⟩ :: stackLabels ⟨stack⟩
      let go σ op := do runOp locals (←σ) op
      let es' ← ops.foldl go $ pure innerStack
      if resultsTypecheck ts $ stackValues ⟨es'⟩
        then pure $ stackValues ⟨es'⟩ ++ stack
        else throw .stack_incompatible_with_results
    | .loop ts ops => do
      let innerStack :=
        .label ⟨ts.length, [.loop ts ops]⟩ :: stackLabels ⟨stack⟩
      let go σ op := do runOp locals (←σ) op
      let es' ← ops.foldl go $ pure innerStack
      if resultsTypecheck ts $ stackValues ⟨es'⟩
        then pure $ stackValues ⟨es'⟩ ++ stack
        else throw .stack_incompatible_with_results
    | .if ts thens elses => do
      let (stack', cond) ← getSO locals stack .from_stack
      match cond with
      | .num (.i ⟨32, n⟩) =>
        -- Reducing to a block is actually spec-conforming behaviour!
        runOp locals stack' $ .block ts (if n ≠ 0 then thens else elses)
      | _ => throw .typecheck_failed
end

def runDo (_s : Store m)
          (f : FunctionInstance m)
          (σ : Stack)
          : Except EngineErrors Stack := do
  let bite acc x := do
    match (←acc).1.es with
    | [] => .error .not_enough_stuff_on_stack
    | y :: rest =>
      if stackEntryTypecheck x.type y
      then .ok (⟨rest⟩, y :: (←acc).2)
      else .error .param_type_incompatible
  let pσ ← f.params.foldl bite $ .ok (σ, [])
  let locals := (f.params ++ f.locals).map
    fun l => (l.name, pσ.2.get? l.index)
  let go oσ x:= do Stack.mk <$> runOp locals (←oσ).es x
  f.ops.foldl go $ .ok pσ.1

-- This is sort of a debug function, returning the full resulting stack instead
-- of just the values specified in the result fields.
def runFullStack (s : Store m) (fid : Nat) (σ : Stack) : Except EngineErrors Stack :=
  match s.func.get? fid with
  | .none => .error .function_not_found
  | .some f => runDo s f σ

def run (s : Store m) (fid : Nat) (σ : Stack) : Except EngineErrors Stack :=
  match s.func.get? fid with
  | .none => .error .function_not_found
  | .some f => do
    let rstack ← runDo s f σ
    if resultsTypecheck f.results rstack.es
      then pure rstack
      else throw .stack_incompatible_with_results
