import Wasm.Wast.AST
import Wasm.Wast.Code
import Wasm.Wast.Num
import YatimaStdLib

open Wasm.Wast.AST
open Wasm.Wast.AST.Func
open Wasm.Wast.AST.Global
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
| local_with_given_name_missing : String → EngineErrors
| local_with_given_id_missing : Nat → EngineErrors
| global_with_given_name_missing : String → EngineErrors
| global_with_given_id_missing : Nat → EngineErrors
| cant_mutate_const_global
| label_not_found
| function_not_found
| other -- JACKAL

instance : ToString EngineErrors where
  toString x := match x with
  | .not_enough_stuff_on_stack => "not enough stuff on stack"
  | .stack_incompatible_with_results => "stack incompatible with result types"
  | .param_type_incompatible => "param type incompatible"
  | .typecheck_failed => s!"typecheck failed"
  | .local_with_given_id_missing i => s!"local #{i} not found"
  | .local_with_given_name_missing n => s!"local ``{n}'' not found"
  | .global_with_given_id_missing i => s!"global #{i} not found"
  | .global_with_given_name_missing n => s!"global ``{n}'' not found"
  | .cant_mutate_const_global => "cannot change value of a const global"
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

namespace GlobalInstance

/-
`val` is of type `NumUniT` because locals need to be of a value type,
and `StackEntry`s can e.g. be labels.
TODO: change `NumUniT` to a full value type when we add vectors.
-/
structure GlobalInstance where
  name  : Option String
  val   : Option NumUniT
  type  : GlobalType
deriving BEq

end GlobalInstance
open GlobalInstance

abbrev Globals := List GlobalInstance

def instantiateGlobals (gs : List Global) : Globals :=
  gs.map fun g =>
    let val := match g.init with
    | .const _t cv => cv
    | _ => unreachable! -- TODO: global.get case
    ⟨g.name, val, g.type⟩

def findGlobalByName? (gs : Globals) (x : String) : Option GlobalInstance :=
  gs.find? (.some x == ·.name)

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
  globals : Globals
  func : List (FunctionInstance m)

def mkStore (m : Module) : Store m :=
  ⟨instantiateGlobals m.globals, instantiateFs m⟩

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

namespace LocalEntry

/-
`val` is of type `NumUniT` because locals need to be of a value type,
and `StackEntry`s can e.g. be labels.
TODO: change `NumUniT` to a full value type when we add vectors.
-/
structure LocalEntry where
  name : Option String
  val  : Option NumUniT
  type : Type'
deriving BEq

end LocalEntry
open LocalEntry

abbrev Locals := List LocalEntry

def findLocalByName? (ls : Locals) (x : String) : Option LocalEntry :=
  ls.find? (.some x == ·.name)

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
  ExceptT Continuation $ StateT (List StackEntry) $
    StateT Locals $ StateT Globals $ Except EngineErrors

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

def getLocals : EngineM Locals := getThe Locals
def modifyLocals (f : Locals → Locals) : EngineM PUnit := modifyThe Locals f
def setLocals (ls : Locals) : EngineM PUnit := modifyLocals fun _ => ls

def checkreplaceLocals (replace : Locals → LocalEntry → LocalEntry → Locals)
                       (err : EngineErrors)
                       : StackEntry → Option LocalEntry → EngineM PUnit
  | se@(.num n), .some l =>
    if stackEntryTypecheck l.type se
    then modifyLocals (replace · l {l with val := .some n})
    else throwEE .param_type_incompatible
  | .num _, _ => throwEE err
  | _, _ => throwEE .typecheck_failed

def getGlobals : EngineM Globals := getThe Globals
def modifyGlobals (f : Globals → Globals) : EngineM PUnit := modifyThe Globals f
def setGlobals (ls : Globals) : EngineM PUnit := modifyGlobals fun _ => ls

def checkreplaceGlobals
        (replace : Globals → GlobalInstance → GlobalInstance → Globals)
        (err : EngineErrors)
        : StackEntry → Option GlobalInstance → EngineM PUnit
  | se@(.num n), .some g =>
    if !g.type.mut? then throwEE .cant_mutate_const_global
    else
      if stackEntryTypecheck g.type.type se
      then modifyGlobals (replace · g {g with val := .some n})
      else throwEE .param_type_incompatible
  | .num _, _ => throwEE err
  | _, _ => throwEE .typecheck_failed

mutual

  partial def getSO : Get' → EngineM StackEntry
    | .from_stack => bite
    | .from_operation o => do runOp o; bite

  partial def computeContinuation
                    (blocktypes : List Type') (ops' : List Operation)
                    : EngineM PUnit := do
    let rec go
    | [] => pure ()
    | op :: ops => do match ←(runOp op).run (←get) with
      | (.error cont, stack') => set stack'; go cont
      | (.ok _, stack') => set stack'; go ops

    go ops'
    let es' := stackValues ⟨←get⟩
    if resultsTypecheck blocktypes es'
      then set es'
      else throwEE .stack_incompatible_with_results

  -- TODO: check that typechecking is done everywhere!
  partial def runOp : Operation → EngineM PUnit := fun op =>
    let runIUnop g unop := do
      match (←getSO g) with
        -- TODO: check bitsize and overflow!
      | .num (.i ⟨b, i⟩) =>
          push $ .num $ .i ⟨b, unop i⟩
      | _ => throwEE .param_type_incompatible
    let runIBinop g0 g1 binop := do
      let operand0 ← getSO g0
      let operand1 ← getSO g1
      match operand0, operand1 with
        -- TODO: check bitsize and overflow!
      | .num (.i ⟨b0, i0⟩), .num (.i ⟨_b1, i1⟩) =>
          push $ .num $ .i ⟨b0, binop i0 i1⟩
      | _, _ => throwEE .param_type_incompatible
    let runFBinop g0 g1 binop := do -- sad we can't generalise over constructors
      let operand0 ← getSO g0
      let operand1 ← getSO g1
      match operand0, operand1 with
        -- TODO: check bitsize and overflow!
      | .num (.f ⟨b0, f0⟩), .num (.f ⟨_b1, f1⟩) =>
          push $ .num $ .f ⟨b0, binop f0 f1⟩
      | _, _ => throwEE .param_type_incompatible
    let blockOp ts ops contLabel := do
      let innerStack := contLabel :: stackLabels ⟨←get⟩
      let es' ← (computeContinuation ts ops).run innerStack
      pile es'.2
    let unsigned (f : Int → Int → Int) (t : Type') := fun x y =>
      match t with
      | .i bs => f (unsign x bs) (unsign y bs)
      | .f _ => unreachable!
    let checkTop_i32 (f : Int → EngineM PUnit) := do
      match (←getSO .from_stack) with
      | .num (.i ⟨32, n⟩) => f n
      | _ => throwEE .typecheck_failed
    let checkLabel (li : LabelIndex) (f : Label → EngineM PUnit) := do
      match fetchLabel ⟨←get⟩ li with
      | .none => throwEE .label_not_found
      | .some label => f label

    match op with
    | .nop => pure ⟨⟩
    | .drop => discard bite
    | .const _t n => push $ .num n
    | .eqz _t g => runIUnop g $ (if · = 0 then 1 else 0)
    | .eq (.i _) g0 g1 => runIBinop g0 g1 (if · = · then 1 else 0)
    | .eq (.f _) g0 g1 => runFBinop g0 g1 (if · == · then 1 else 0) -- lmao even this isn't right because of +0 == -0
    | .ne (.i _) g0 g1 => runIBinop g0 g1 (if · ≠ · then 1 else 0)
    | .ne (.f _) g0 g1 => runFBinop g0 g1 (if · != · then 1 else 0)
    | .lt_u t  g0 g1 => runIBinop g0 g1 $ unsigned (if · < · then 1 else 0) t
    | .lt_s _t g0 g1 => runIBinop g0 g1 (if · < · then 1 else 0)
    | .gt_u t  g0 g1 => runIBinop g0 g1 $ unsigned (if · > · then 1 else 0) t
    | .gt_s _t g0 g1 => runIBinop g0 g1 (if · > · then 1 else 0)
    | .le_u t  g0 g1 => runIBinop g0 g1 $ unsigned (if · ≤ · then 1 else 0) t
    | .le_s _t g0 g1 => runIBinop g0 g1 (if · ≤ · then 1 else 0)
    | .ge_u t  g0 g1 => runIBinop g0 g1 $ unsigned (if · ≥ · then 1 else 0) t
    | .ge_s _t g0 g1 => runIBinop g0 g1 (if · ≥ · then 1 else 0)
    | .lt _t g0 g1 => runFBinop g0 g1 (if · < · then 1 else 0)
    | .gt _t g0 g1 => runFBinop g0 g1 (if · > · then 1 else 0)
    | .le _t g0 g1 => runFBinop g0 g1 (if · ≤ · then 1 else 0)
    | .ge _t g0 g1 => runFBinop g0 g1 (if · ≥ · then 1 else 0)
    | .clz t g => runIUnop g fun i =>
      ((toNBits i $ bitsize t).takeWhile (· = .zero)).length
    | .ctz t g => runIUnop g fun i =>
      ((toNBits i $ bitsize t).reverse.takeWhile (· = .zero)).length
    | .popcnt t g => runIUnop g fun i =>
      ((toNBits i $ bitsize t).filter (· = .one)).length
    | .add (.i _) g0 g1 => runIBinop g0 g1 (· + ·)
    | .add (.f _) g0 g1 => runFBinop g0 g1 (· + ·)
    | .sub (.i _) g0 g1 => runIBinop g0 g1 (· - ·)
    | .sub (.f _) g0 g1 => runFBinop g0 g1 (· - ·)
    | .mul (.i _) g0 g1 => runIBinop g0 g1 (· * ·)
    | .mul (.f _) g0 g1 => runFBinop g0 g1 (· * ·)
    | .div _t g0 g1 => runFBinop g0 g1 (· / ·)
    | .max _t g0 g1 => runFBinop g0 g1 max
    | .min _t g0 g1 => runFBinop g0 g1 min
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
    | .local_get (.by_index idx) => do match (←getLocals).get? idx with
      | .some ⟨_, .some n, _⟩ => push $ .num n
      | _ => throwEE $ .local_with_given_id_missing idx
    | .local_get (.by_name name) => do
      match findLocalByName? (←getLocals) name with
      | .some ⟨_, .some n, _⟩ => push $ .num n
      | _ => throwEE $ .local_with_given_name_missing name
    | .local_set (.by_index idx) => do
          -- we can't use locals.replace because that one replaces
          -- _the first_ occurrence, which might be earlier than on the idx
        checkreplaceLocals (fun locals _ => replaceNth locals idx)
          (.local_with_given_id_missing idx) (←bite) ((←getLocals).get? idx)
    | .local_set (.by_name name) => do
        checkreplaceLocals List.replace (.local_with_given_name_missing name)
          (←bite) (findLocalByName? (←getLocals) name)
    | .local_tee l => do match ←bite with
      | val@(.num _) => push val; push val; runOp $ .local_set l
      | _ => throwEE .typecheck_failed
    | .global_get (.by_index idx) => do match (←getGlobals).get? idx with
      | .some ⟨_, .some n, _⟩ => push $ .num n
      | _ => throwEE $ .global_with_given_id_missing idx
    | .global_get (.by_name name) => do
      match findGlobalByName? (←getGlobals) name with
      | .some ⟨_, .some n, _⟩ => push $ .num n
      | _ => throwEE $ .global_with_given_name_missing name
    | .global_set (.by_index idx) => do
        checkreplaceGlobals (fun globals _ => replaceNth globals idx)
          (.global_with_given_id_missing idx) (←bite) ((←getGlobals).get? idx)
    | .global_set (.by_name name) => do
        checkreplaceGlobals List.replace (.global_with_given_name_missing name)
          (←bite) (findGlobalByName? (←getGlobals) name)
    | .block ts ops => blockOp ts ops $ .label ⟨ts.length, []⟩
      -- TODO: currently, we only support simple [] → [valuetype*] blocks,
      -- not type indices. For this reason, we start the block execution
      -- with an stack devoid of _values_ to simulate 0-input-arity, but we
      -- still pass in all the labels currently reachable.
    | .loop ts ops => blockOp ts ops $ .label ⟨ts.length, [.loop ts ops]⟩
    | .if ts thens elses => checkTop_i32 fun n =>
      runOp $ .block ts (if n ≠ 0 then thens else elses)
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
        if n = 0 then pure () else runOp (.br li)
end

def runDo (s : Store m)
          (f : FunctionInstance m)
          (σ : Stack)
          : Except EngineErrors (Globals × Stack) := do
  let bite acc x := do
    match (←acc).1 with
    | [] => .error .not_enough_stuff_on_stack
    | .num y :: rest =>
      if stackEntryTypecheck x.type $ .num y
      then .ok (rest, y :: (←acc).2)
      else .error .param_type_incompatible
    | _ :: _ => .error .param_type_incompatible
  let pσ ← f.params.foldl bite $ .ok (σ.es, [])
  let locals := (f.params ++ f.locals).map
    fun l => ⟨l.name, pσ.2.get? l.index, l.type⟩
  let ses ← (f.ops.forM runOp).run pσ.1 locals s.globals
  pure (ses.2, Stack.mk ses.1.1.2)

-- This is sort of a debug function, returning the full resulting stack instead
-- of just the values specified in the result fields.
def runFullStack (s : Store m) (fid : Nat) (σ : Stack) : Except EngineErrors (Globals × Stack) :=
  match s.func.get? fid with
  | .none => .error .function_not_found
  | .some f => runDo s f σ

def run (s : Store m) (fid : Nat) (σ : Stack) : Except EngineErrors (Globals × Stack) :=
  match s.func.get? fid with
  | .none => .error .function_not_found
  | .some f => do
    let res ← runDo s f σ
    if resultsTypecheck f.results res.2.es
      then pure res
      else throw .stack_incompatible_with_results
