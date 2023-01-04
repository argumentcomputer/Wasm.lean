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
| label_not_found
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
  | .label_not_found => s!"label not found"
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

/- This is a readability helper type abbreviation for use in handling
flow correctly when executing branch instructions like `br` and `br_if`.

The `List Operation` in the return type represents an optional 'final'
sequence of instructions – which should replace the rest of the instructions
in the currently executed sequence, which in turn emulates the continuation
jump, except it's more like 'continuation unwinding'.

Semantics:
- `.none` means there is no continuation, like in most simple/data instructions.
- `some []` means there is a continuation, but it is empty, ending the block.
- `some ops` means "drop the rest of whatever you're doing and run this instead"
-/
abbrev ContinuationStack := (List StackEntry × Option (List Operation))

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
                    : Get'
                    → Except EngineErrors (ContinuationStack × StackEntry)
    | .from_stack => match stack with
      | [] => .error .not_enough_stuff_on_stack
      | s :: rest => .ok ((rest, .none), s)
    | .from_operation o => do
      -- Some instructions do not produce a value/do not change stack.
      let (stack', cont?) ← runOp locals stack o
      match stack' with
      | [] =>
        if cont?.isSome
          then throw .other -- TODO: this is incorrect! It's possible to `br` to
                            -- a resultless block, in which case the empty stack
                            -- should be returned with the continuation, but rn
                            -- it's not possible. Continuations should ideally
                            -- be passed in a monadic way, not this jackally.
          else throw .not_enough_stuff_on_stack
      | s :: rest => pure ((rest, cont?), s)
    -- TODO: names are erased in production. See what do we want to do with this code path.
    | .by_name n => match n.name with
      | .none => .error .local_with_no_name_given
      | .some name => match findLocalByName? locals name with
        | .none => .error $ .local_with_given_name_missing name
        | .some l => .ok ((stack, .none), l)
    | .by_index i => match locals.get? i.index with
      | .some (_, .some se)  => .ok ((stack, .none), se)
      | _ => .error $ .local_with_given_id_missing i.index

  partial def runWithContinuation
                      (blocktypes : List Type')
                      (locals : List (Option String × Option StackEntry))
                      (so : ContinuationStack)
                      (ops' : List Operation)
                      : Except EngineErrors (List StackEntry) := do
    let rec go
    | (stack, .none), [] => pure stack
    | (stack, .some cont), _ => go (stack, .none) cont
    | (stack, .none), op :: ops => do go (←runOp locals stack op) ops

    let es' ← (stackValues ∘ Stack.mk) <$> go so ops'
    if resultsTypecheck blocktypes es'
      then pure es'
      else throw .stack_incompatible_with_results

  -- TODO: this `getSO` threading shit literally simulates a monad in a way.
  -- We NEED to rewrite continuations to be passed more sanely.
  -- (`ContinuationStack` monad? `Except` pulling double-weight?)
  partial def runIBinop (locals : List (Option String × Option StackEntry))
                        (stack : List StackEntry)
                        (g0 : Get') (g1 : Get')
                        (binop : Int → Int → Int)
                        : Except EngineErrors ContinuationStack := do
    let ((stack', cont?), operand0) ← getSO locals stack g0
    if cont?.isSome then pure (operand0 :: stack', cont?) else
      let ((stack1, cont1?), operand1) ← getSO locals stack' g1
      if cont1?.isSome then pure (operand1 :: stack1, cont1?) else
        let res ← match operand0, operand1 with
          -- TODO: check bitsize and overflow!
          | .num (.i ⟨b0, i0⟩), .num (.i ⟨_b1, i1⟩) =>
              pure $ .num $ .i ⟨b0, binop i0 i1⟩
          | _, _ => throw .param_type_incompatible
        pure (res :: stack1, .none)

  -- TODO: there's a StateT somewhere here. Just sayin'
  -- TODO: we're not typechecking at all!
  -- TODO: can locals change when executing nested instructions?
  partial def runOp (locals : List (Option String × Option StackEntry))
                    (stack : List StackEntry)
                    : Operation
                    → Except EngineErrors ContinuationStack
    | .nop => pure (stack, .none)
    | .const _t n => pure (.num n :: stack, .none)
    | .add _t g0 g1 => runIBinop locals stack g0 g1 fun x y => x+y
    | .block ts ops => do
      -- TODO: currently, we only support simple [] → [valuetype*] blocks,
      -- not type indices. For this reason, we start the block execution
      -- with an stack devoid of _values_ to simulate 0-input-arity, but we
      -- still pass in all the labels currently reachable.
      let innerStack := .label ⟨ts.length, []⟩ :: stackLabels ⟨stack⟩
      let es' ← runWithContinuation ts locals (innerStack, .none) ops
      pure (es' ++ stack, .none)
    | .loop ts ops => do
      let innerStack :=
        .label ⟨ts.length, [.loop ts ops]⟩ :: stackLabels ⟨stack⟩
      let es' ← runWithContinuation ts locals (innerStack, .none) ops
      pure (es' ++ stack, .none)
    | .if ts thens elses => do
      let ((stack', _), cond) ← getSO locals stack .from_stack
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
  let go oσ x:= do (fun so => Stack.mk so.1) <$> runOp locals (←oσ).es x
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
