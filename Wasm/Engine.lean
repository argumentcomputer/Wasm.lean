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

/-
The `List Operation` in the `Continuation` type represents an optional 'final'
sequence of instructions – which should replace the rest of the instructions
in the currently executed sequence, which in turn emulates the continuation
jump, except it's more like 'continuation unwinding'.

Semantics:
- `.ok` means there is no continuation, like in most simple/data instructions.
- `.error []` means there is a continuation, but it is empty, ending the block.
- `.error ops` means "drop the rest of what you're doing and run this instead"

-------------/
abbrev Continuation := List Operation

/-
This is a readability helper monad stack abbreviation for use in handling
flow correctly when executing branch instructions like `br` and `br_if`,
as well as just for easy handling of the stack and possible errors.

The monads in the stack:
- `Except EngineErrors` throws _real_ execution errors. It's on the very bottom
  of the stack because we don't care about anything else, like recovery, if
  there's an engine error.
- `StateT (List StackEntry)` carries the stack around for ease of handling.
- `ExceptT Continuation` doesn't handle real exceptions, instead it serves as
  a way to throw continuations through the execution cycle like described above.
  It's the outermost transformer because when a continuation throw does occur,
  we want both the `Continuation` and the `List StackEntry` that comes with it
  from the `StateT` layer.

-/
abbrev EngineM :=
  ExceptT Continuation (StateT (List StackEntry) (Except EngineErrors))

instance : Inhabited (EngineM α) where
  default := throw default

def throwEE : EngineErrors → EngineM α := ExceptT.lift ∘ throw
def raiseCont : List Operation → EngineM α := throw

def bite : EngineM StackEntry := do match (←get) with
  | [] => throwEE .not_enough_stuff_on_stack
  | s :: rest => set rest; pure s
def push : StackEntry → EngineM PUnit := fun x => do set $ x :: (←get)
def pile : List StackEntry → EngineM PUnit := fun xs => do set $ xs ++ (←get)
def σmap : (List StackEntry → List StackEntry) → EngineM PUnit :=
  fun f => do set $ f (←get)

mutual

  partial def getSO (locals : List (Option String × Option StackEntry))
                    : Get' → EngineM StackEntry
    | .from_stack => bite
    | .from_operation o => do runOp locals o; bite
    -- TODO: names are erased in production. See what do we want to do with this code path.
    | .by_name n => match n.name with
      | .none => throwEE .local_with_no_name_given
      | .some name => match findLocalByName? locals name with
        | .none => throwEE $ .local_with_given_name_missing name
        | .some l => pure l
    | .by_index i => match locals.get? i.index with
      | .some (_, .some se) => pure se
      | _ => throwEE $ .local_with_given_id_missing i.index

  partial def computeContinuation
                      (blocktypes : List Type')
                      (locals : List (Option String × Option StackEntry))
                      (ops' : List Operation)
                      : EngineM PUnit := do
    let rec go
    | [] => pure ()
    | op :: ops => do match ←(runOp locals op).run (←get) with
      | (.error cont, stack') => set stack'; go cont
      | (.ok _, stack') => set stack'; go ops

    go ops'
    let es' := stackValues ⟨←get⟩
    if resultsTypecheck blocktypes es'
      then set es'
      else throwEE .stack_incompatible_with_results

  -- TODO: check that typechecking is done everywhere!
  partial def runOp (locals : List (Option String × Option StackEntry))
                    : Operation → EngineM PUnit := fun op =>
    let runIBinop g0 g1 binop := do
      let operand0 ← getSO locals g0
      let operand1 ← getSO locals g1
      match operand0, operand1 with
        -- TODO: check bitsize and overflow!
      | .num (.i ⟨b0, i0⟩), .num (.i ⟨_b1, i1⟩) =>
          push $ .num $ .i ⟨b0, binop i0 i1⟩
      | _, _ => throwEE .param_type_incompatible
    let blockOp ts ops contLabel := do
      let innerStack := contLabel :: stackLabels ⟨←get⟩
      let es' ← (computeContinuation ts locals ops).run innerStack
      pile es'.2
    let unsigned (f : Int → Int → Int) (t : Type') := fun x y =>
      match t with
      | .i bs => f (unsign x bs) (unsign y bs)
      | .f _ => unreachable!
    let checkTop_i32 (f : Int → EngineM PUnit) := do
      match (←getSO locals .from_stack) with
      | .num (.i ⟨32, n⟩) => f n
      | _ => throwEE .typecheck_failed
    let checkLabel (li : LabelIndex) (f : Label → EngineM PUnit) := do
      match fetchLabel ⟨←get⟩ li with
      | .none => throwEE .label_not_found
      | .some label => f label

    match op with
    | .nop => pure ⟨⟩
    | .const _t n => push $ .num n
    -- TODO: run NOT IBinop depending on the type
    | .add _t g0 g1 => runIBinop g0 g1 (· + ·)
    | .sub _t g0 g1 => runIBinop g0 g1 (· - ·)
    | .mul _t g0 g1 => runIBinop g0 g1 (· * ·)
    | .div_s _t g0 g1 => runIBinop g0 g1 (· / ·)
    | .div_u  t g0 g1 => runIBinop g0 g1 $ unsigned (· / ·) t
    | .rem_s _t g0 g1 => runIBinop g0 g1 (· % ·)
    | .rem_u  t g0 g1 => runIBinop g0 g1 $ unsigned (· % ·) t
    | .and _t g0 g1 => runIBinop g0 g1 (· &&& ·)
    | .or _t g0 g1  => runIBinop g0 g1 (· ||| ·)
    | .xor _t g0 g1 => runIBinop g0 g1 (· ^^^ ·)
    | .shl _t g0 g1 => runIBinop g0 g1 (· <<< ·)
    | .shr_u t g0 g1 => runIBinop g0 g1 $ unsigned (· >>> ·) t
    | .shr_s (.i bs) g0 g1 => runIBinop g0 g1 fun x k =>
      let N := (2 : Int)^(bs : Nat)
      (x >>> k) ||| (x &&& (N/2))
    | .shr_s _ _ _ => throwEE .typecheck_failed
    | .rotl (.i bs) g0 g1 => runIBinop g0 g1 fun x k =>
      (x <<< k) ||| match k with
      | .ofNat   _ => (x >>> ((bs : Int) - k))
      | .negSucc _ => (x <<< ((bs : Int) + k))
    | .rotl _ _ _ => throwEE .typecheck_failed
    | .rotr (.i bs) g0 g1 => runIBinop g0 g1 fun x k =>
      (x >>> k) ||| match k with
      | .ofNat   _ => x <<< ((bs : Int) - k)
      | .negSucc _ => x >>> ((bs : Int) + k)
    | .rotr _ _ _ => throwEE .typecheck_failed
    | .block ts ops => blockOp ts ops $ .label ⟨ts.length, []⟩
      -- TODO: currently, we only support simple [] → [valuetype*] blocks,
      -- not type indices. For this reason, we start the block execution
      -- with an stack devoid of _values_ to simulate 0-input-arity, but we
      -- still pass in all the labels currently reachable.
    | .loop ts ops => blockOp ts ops $ .label ⟨ts.length, [.loop ts ops]⟩
    | .if ts thens elses => checkTop_i32 fun n =>
      runOp locals $ .block ts (if n ≠ 0 then thens else elses)
    | .br li => checkLabel li fun ⟨n, cont⟩ => do
      let (topn, rest) := (←get).splitAt n
      if (stackValues ⟨topn⟩).length = n
        then match skimValues ⟨rest⟩ with
          | .label _ :: bottom =>
            set $ topn ++ bottom
            raiseCont $ if li = ⟨0⟩ then cont else [.br ⟨li.li-1⟩]
          | _ => throwEE .typecheck_failed
        else throwEE .not_enough_stuff_on_stack
    | .br_if li => checkTop_i32 fun n =>
        if n = 0 then pure () else runOp locals (.br li)
end

def runDo (_s : Store m)
          (f : FunctionInstance m)
          (σ : Stack)
          : Except EngineErrors Stack := do
  let bite acc x := do
    match (←acc).1 with
    | [] => .error .not_enough_stuff_on_stack
    | y :: rest =>
      if stackEntryTypecheck x.type y
      then .ok (rest, y :: (←acc).2)
      else .error .param_type_incompatible
  let pσ ← f.params.foldl bite $ .ok (σ.es, [])
  let locals := (f.params ++ f.locals).map
    fun l => (l.name, pσ.2.get? l.index)
  let ses ← (f.ops.forM fun op => discard $ runOp locals op).run pσ.1
  pure $ Stack.mk ses.2

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
