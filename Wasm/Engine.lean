import Wasm.Wast.AST
import Wasm.Wast.Code
import Wasm.Wast.Num
import YatimaStdLib.Cached
import YatimaStdLib.Int

open Wasm.Wast.AST
open Wasm.Wast.AST.Func
open Wasm.Wast.AST.Global
open Wasm.Wast.AST.FuncLabel
open Wasm.Wast.AST.BlockLabel
open Wasm.Wast.AST.Local
open Wasm.Wast.AST.Module
open Wasm.Wast.AST.Operation
open Wasm.Wast.Code
open Wasm.Wast.Num.Uni
open Cached

namespace Wasm.Engine

inductive EngineErrors where
| unreachable
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
| function_not_found : FuncId → EngineErrors
| other -- JACKAL

instance : ToString EngineErrors where
  toString x := match x with
  | .unreachable => "unreachable"
  | .not_enough_stuff_on_stack => "not enough stuff on stack"
  | .stack_incompatible_with_results => "stack incompatible with result types"
  | .param_type_incompatible => "param type incompatible"
  | .typecheck_failed => s!"typecheck failed"
  | .local_with_given_id_missing i => s!"local #{i} not found"
  | .local_with_given_name_missing n => s!"local ``{n}'' not found"
  | .global_with_given_id_missing i => s!"global #{i} not found"
  | .global_with_given_name_missing n => s!"global ``{n}'' not found"
  | .cant_mutate_const_global => "cannot change value of a const global"
  | .function_not_found fid => s!"function not found: {fid}"
  | .label_not_found => s!"label not found"
  | .other => "non-specified"

instance : Inhabited EngineErrors where
  default := .other

namespace StackEntry

inductive StackEntry where
| num : NumUniT → StackEntry
| label : BlockLabel → StackEntry

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

def shadowLabel (es : List StackEntry) : Option String → List StackEntry
  | .none => es
  | .some s =>
    let go
      | .label l => if l.name = .some s
          then .label {l with name := .none}
          else .label l
      | other => other
    es.map go

def skimValues (stack : Stack) : List StackEntry :=
  stack.es.dropWhile isValue

-- When a label is found, returns not only that label but also its depth.
-- Necessary for `.by_name` lookup
def fetchLabel (stack : Stack) : BlockLabelId → Option (BlockLabel × Nat)
  | .by_index li =>
    let rec go
      | [], _ => .none
      | .label l :: _, 0 => .some (l, li)
      | .num _ :: es, n => go es n
      | .label _ :: es, n+1 => go es n
    go stack.es li
  | .by_name s =>
    let findLabelById
      | (idx, .label l) => if l.name = .some s then .some (l, idx) else .none
      | _ => .none
    stack.es.enum.findSome? findLabelById

namespace GlobalInstance

/-
`val` is of type `NumUniT` because locals need to be of a value type,
and `StackEntry`s can e.g. be labels.
TODO: change `NumUniT` to a full value type when we add vectors.
-/
structure GlobalInstance where
  name  : Option String
  val   : NumUniT
  type  : GlobalType
deriving BEq

end GlobalInstance
open GlobalInstance

abbrev Globals := List GlobalInstance

def instantiateGlobals (gs : List Global) : Globals :=
  gs.map fun g =>
    let val := match g.init with
    | .const _t cv => cv
    | _ => sorry -- TODO: global.get case
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
    let fi := FunctionInstance.mk f.name
                                  f.export_
                                  f.params
                                  f.results
                                  f.locals
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

def exportedFuncByName (s : Store m) (x : String)
                       : Option $ FunctionInstance m :=
  s.func.find? (·.export_ = .some x)

def exportedFidByName (s : Store m) (x : String) : Option Nat :=
  FunctionInstance.index <$> exportedFuncByName s x

/-- Find a `FunctionInstance` by a function id/address "getter".
Note that in case of by name lookup this searches function
_symbolic identifiers_ instead of _export_ names. -/
def fetchFAddress (s : Store m) : FuncId → Option (FunctionInstance m)
  | .by_index i => s.func.get? i
  | .by_name name => s.func.find? (·.name = .some name)

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

/-- Checks that the given numerical values correspond to the given
types both in the type of each respective value and in length. -/
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
  val  : NumUniT
  type : Type'
deriving BEq

end LocalEntry
open LocalEntry

abbrev Locals := List LocalEntry

/--
`local` variables are initialised with their default values,
i.e. `0` for number types.
 -/
def initLocal (l : Local) : LocalEntry := ⟨l.name, defNum l.type, l.type⟩

def findLocalByName? (ls : Locals) (x : String) : Option LocalEntry :=
  ls.find? (.some x == ·.name)

namespace ActivationFrame

structure Frame where
  arity  : Nat
  locals : Locals
deriving BEq, Inhabited

end ActivationFrame
open ActivationFrame

/-- A "tag" inductive to simulate a `return` instruction. -/
inductive Return where | return
  deriving Inhabited, BEq

/--
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

variable {m : Module}

/--
This is a readability helper monad stack abbreviation for use in handling
flow correctly when executing branch instructions like `br` and `br_if`,
as well as just for easy handling of the stack and possible errors.

The monads in the stack:
- `Except EngineErrors` throws _real_ execution errors. It's on the very bottom
  of the stack because we don't care about anything else, like recovery, if
  there's an engine error.
- `StateT` monads carry mutable values around for ease of handling:
    - `StateT Frame` carries the current function arity and its locals.
    - `StateT (Store m)` carries the function instances we might need for `call`
  and the module `GlobalInstance`s.
    - `StateT (List StackEntry)` carries the stack: numerical values and block
    labels. Note that we don't put activation frames on stack like in the spec.
- `ExceptT Continuation` doesn't handle real exceptions, instead it serves as
  a way to throw structured control instruction continuations through the
  execution cycle like described above.
  It's the outer transformer because when a continuation throw does occur,
  we want both the `Continuation` and the `List StackEntry` that comes with it
  from the `StateT` layer.
- `ExceptT Return` is the same as above, but for function invocations.

-/
abbrev EngineM m :=
  ExceptT Return $ ExceptT Continuation $ StateT (List StackEntry) $
    StateT Frame $ StateT (Store m) $ Except EngineErrors

def throwEE : EngineErrors → EngineM m α := ExceptT.lift ∘ ExceptT.lift ∘ throw
def raiseCont : List Operation → EngineM m α := ExceptT.lift ∘ throw
def raiseReturn : EngineM m α := throw default

instance : Inhabited (EngineM m α) where
  default := throwEE .other

def bite : EngineM m StackEntry := do match (←get) with
  | [] => throwEE .not_enough_stuff_on_stack
  | s :: rest => set rest; pure s
def push : StackEntry → EngineM m PUnit := fun x => do set $ x :: (←get)
def pile : List StackEntry → EngineM m PUnit := fun xs => do set $ xs ++ (←get)
def σmap : (List StackEntry → List StackEntry) → EngineM m PUnit :=
  fun f => do set $ f (←get)

def getFrame : EngineM m Frame := getThe Frame
def modifyFrame (f : Frame → Frame) : EngineM m PUnit := modifyThe Frame f
def setFrame (ls : Frame) : EngineM m PUnit := modifyFrame fun _ => ls

def getArity : EngineM m Nat := Frame.arity <$> getFrame

def getLocals : EngineM m Locals := Frame.locals <$> getFrame
def modifyLocals (f : Locals → Locals) : EngineM m PUnit :=
  modifyFrame fun a => {a with locals := f a.locals}
def setLocals (ls : Locals) : EngineM m PUnit := modifyLocals fun _ => ls

def checkreplaceLocals (replace : Locals → LocalEntry → LocalEntry → Locals)
                       (err : EngineErrors)
                       : StackEntry → Option LocalEntry → EngineM m PUnit
  | se@(.num n), .some l =>
    if stackEntryTypecheck l.type se
    then modifyLocals (replace · l {l with val := n})
    else throwEE .param_type_incompatible
  | .num _, _ => throwEE err
  | _, _ => throwEE .typecheck_failed

def getStore : EngineM m (Store m) := getThe (Store m)
def modifyStore (f : Store m → Store m) : EngineM m PUnit :=
  modifyThe (Store m) f
def setStore (s : Store m) : EngineM m PUnit := modifyStore fun _ => s

def getGlobals : EngineM m Globals := do pure (←getStore).globals
def modifyGlobals (f : Globals → Globals) : EngineM m PUnit :=
  modifyStore fun s => {s with globals := f s.globals}
def setGlobals (gs : Globals) : EngineM m PUnit := modifyGlobals fun _ => gs

def checkreplaceGlobals
        (replace : Globals → GlobalInstance → GlobalInstance → Globals)
        (err : EngineErrors)
        : StackEntry → Option GlobalInstance → EngineM m PUnit
  | se@(.num n), .some g =>
    if !g.type.mut? then throwEE .cant_mutate_const_global
    else
      if stackEntryTypecheck g.type.type se
      then modifyGlobals (replace · g {g with val := n})
      else throwEE .param_type_incompatible
  | .num _, _ => throwEE err
  | _, _ => throwEE .typecheck_failed

def checkLabel (l : BlockLabelId) (f : BlockLabel → Nat → EngineM m PUnit) := do
  match fetchLabel ⟨←get⟩ l with
  | .none => throwEE .label_not_found
  | .some (label, depth) => f label depth

/-- Taking a list of "in" types from the params list, get enough _values_
from the stack. This passes all block label type stack entries to the inner
stack, while preserving those labels "above" the last needed value in the
outer stack. -/
partial def populateBlockParams (ps : List Local)
            : EngineM m (List StackEntry) := do
  let rec go is
    | []    => pure is.toList
    | p::ps => do
      match ←bite with
      | l@(.label _) => go (is.push l) (p::ps)
      | n@(.num _) =>
        if stackEntryTypecheck p.type n
          then go (is.push n) ps
          else throwEE .param_type_incompatible

  let innerStack ← go #[] ps
  let restOfLabels := stackLabels ⟨←get⟩
  pure $ innerStack ++ restOfLabels

/-- Taking a list of "in" types from the params list, get enough _values_
from the stack. Per spec, this means if we hit a label, there's not
enough values on the stack to populate the params. -/
partial def populateFuncParams (ps : List Local)
            : EngineM m Locals := do
  let rec go is
    | []    => pure is.toList
    | p::ps => do
      match ←bite with
      | .label _ => throwEE .not_enough_stuff_on_stack
      | n@(.num i) =>
        if stackEntryTypecheck p.type n
          then go (is.push ⟨p.name, i, p.type⟩) ps
          else throwEE .param_type_incompatible

  go #[] ps

def enf2Nums1Type : StackEntry → StackEntry → EngineM m Type'
  | .num (.i ⟨32, _⟩), .num (.i ⟨32, _⟩) => pure $ .i 32
  | .num (.i ⟨64, _⟩), .num (.i ⟨64, _⟩) => pure $ .i 64
  | .num (.f ⟨32, _⟩), .num (.f ⟨32, _⟩) => pure $ .f 32
  | .num (.f ⟨64, _⟩), .num (.f ⟨64, _⟩) => pure $ .f 64
  | _, _ => throwEE .param_type_incompatible

/-- Check that two stack entries are of the same numerical type,
check correctness of this type if given. Throws `.typecheck_failed` otherwise.
-/
def typecheck2Nums (t? : Option Type') (o1 o2: StackEntry) : EngineM m PUnit := do
  let ot ← enf2Nums1Type o1 o2
  if let .some t := t? then
    if t ≠ ot then throwEE .typecheck_failed

def getInt : StackEntry → EngineM m Int
  | .num (.i n) => pure n.val
  | _ => throwEE .typecheck_failed

def unsigned (f : Int → Int → Int) (t : Type') := fun x y =>
  match t with
  | .i bs => f (Int.unsign x bs) (Int.unsign y bs)
  | .f _ => unreachable!

mutual

  partial def getSO : Get' → EngineM m StackEntry
    | .from_stack => bite
    | .from_operation o => do runOp o; bite

  partial def computeContinuation
                    (blocktypes : List Type') (ops' : List Operation)
                    : EngineM m PUnit := do
    let rec go
    | [] => pure ()
    | op :: ops => do match ←(runOp op).run (←get) with
      | (.error cont, stack') => set stack'; go cont
      | (.ok (.error .return), stack') => set stack'; raiseReturn -- rethrow
      | (.ok (.ok ()), stack') => set stack'; go ops

    go ops'
    let es' := stackValues ⟨←get⟩
    if resultsTypecheck blocktypes es'
      then set es'
      else throwEE .stack_incompatible_with_results

  -- TODO: check that typechecking is done everywhere!
  partial def runOp : Operation → EngineM m PUnit := fun op =>
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
    let blockOp ps ts ops contLabel := do
      /- To populate the block type `[valuetypeᵐ] → [valuetype*]`, we start
      the block execution with the inner stack made up of:
      1. the top of the stack up to the `m`th _value_ from the general stack.
         This means it might be interspersed with labels.
      2. The rest of the labels currently reachable. -/
      let innerStack :=
        .label contLabel :: shadowLabel (←populateBlockParams ps) contLabel.name

      -- Block params aren't reachable by variable instructions, so we don't
      -- change the `Locals` part of `EngineM m`.
      let es' ← (computeContinuation ts ops).run innerStack
      pile es'.2
    let checkGet_i32 (g : Get') (f : Int → EngineM m PUnit) := do
      match (←getSO g) with
      | .num (.i ⟨32, n⟩) => f n
      | _ => throwEE .typecheck_failed

    match op with
    | .unreachable => throwEE .unreachable
    | .nop => pure ⟨⟩
    | .drop => discard bite
    | .const _t n => push $ .num n
    | .select t? g0 g1 g2 => checkGet_i32 g0 fun i0 => do
      let operand1 ← getSO g1
      let operand2 ← getSO g2
      typecheck2Nums t? operand1 operand2
      if i0 = 0 then push operand1 else push operand2
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
      ((toNBits i t.bitsize).takeWhile (· = .zero)).length
    | .ctz t g => runIUnop g fun i =>
      ((toNBits i t.bitsize).reverse.takeWhile (· = .zero)).length
    | .popcnt t g => runIUnop g fun i =>
      ((toNBits i t.bitsize).filter (· = .one)).length
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
      | .some ⟨_, n, _⟩ => push $ .num n
      | _ => throwEE $ .local_with_given_id_missing idx
    | .local_get (.by_name name) => do
      match findLocalByName? (←getLocals) name with
      | .some ⟨_, n, _⟩ => push $ .num n
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
      | .some ⟨_, n, _⟩ => push $ .num n
      | _ => throwEE $ .global_with_given_id_missing idx
    | .global_get (.by_name name) => do
      match findGlobalByName? (←getGlobals) name with
      | .some ⟨_, n, _⟩ => push $ .num n
      | _ => throwEE $ .global_with_given_name_missing name
    | .global_set (.by_index idx) => do
        checkreplaceGlobals (fun globals _ => replaceNth globals idx)
          (.global_with_given_id_missing idx) (←bite) ((←getGlobals).get? idx)
    | .global_set (.by_name name) => do
        checkreplaceGlobals List.replace (.global_with_given_name_missing name)
          (←bite) (findGlobalByName? (←getGlobals) name)
    | .block id ps ts ops => blockOp ps ts ops ⟨id, ts.length, []⟩
    | .loop id ps ts ops => blockOp ps ts ops ⟨id, ts.length, [.loop id ps ts ops]⟩
    | .if id ps ts g thens elses => checkGet_i32 g fun n =>
      runOp $ .block id ps ts (if n ≠ 0 then thens else elses)
    | .br l => checkLabel l fun ⟨_, arity, cont⟩ depth => do
      let (topn, rest) := (←get).splitAt arity
      if (stackValues ⟨topn⟩).length = arity
        then match skimValues ⟨rest⟩ with
          | .label _ :: bottom =>
            set $ topn ++ bottom
            raiseCont $ if depth = 0 then cont else [.br $ .by_index (depth-1)]
          | _ => throwEE .typecheck_failed
        else throwEE .not_enough_stuff_on_stack
    | .br_if l => checkGet_i32 .from_stack fun n =>
        do if n ≠ 0 then runOp (.br l)
    | .br_table ls ld => checkGet_i32 .from_stack fun n =>
        if let .some l := ls.get? (n.unsign 32).natAbs
          then runOp (.br l)
          else runOp (.br ld)
    | .call fi => do match fetchFAddress (←getStore) fi with
      | .none => throwEE $ .function_not_found fi
      | .some f => runFunc f
    | .return => do
        let arity ← getArity
        let topn := (←get).take arity
        if topn.length = arity && topn.all isValue
          then set topn
          else throwEE .not_enough_stuff_on_stack
        raiseReturn

  partial def runFunc (f : FunctionInstance m) : EngineM m PUnit := do
    let rec go : List Operation → EngineM m PUnit
      | [] => pure ()
      | op :: ops => do match ←(runOp op).run (←get) with
        | (.error _, _) =>
          -- `br` without a structured control operation – shouldn't be
          -- reachable at all, so throw an `EngineError`.
          throwEE .other
        | (.ok (.error .return), stack') => set stack'
        | (.ok (.ok ()), stack') => set stack'; go ops

    let σ := []
    let locals := (←populateFuncParams f.params) ++ f.locals.map initLocal
    let (res, _) ← (go f.ops).run σ ⟨f.results.length, locals⟩
    if resultsTypecheck f.results res.2
      then pile res.2
      else throwEE .stack_incompatible_with_results

end

def run (s : Store m) (fid : Nat) (σ : Stack)
        : Except EngineErrors (Store m × Stack) :=
  match s.func.get? fid with
  | .none => .error $ .function_not_found (.by_index fid)
  | .some f => do
    let ses ← runFunc f σ.es default s
    pure (ses.2, Stack.mk ses.1.1.2)
