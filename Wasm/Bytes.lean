import Wasm.Wast.AST
import Wasm.Wast.Code
import Wasm.Leb128

open Wasm.Leb128
open Wasm.Wast.Code
open Wasm.Wast.AST
open Wasm.Wast.AST.BlockLabel
open Wasm.Wast.AST.FuncLabel
open Wasm.Wast.AST.FunctionType
open Wasm.Wast.AST.Global
open Wasm.Wast.AST.Local
open Wasm.Wast.AST.Module
open Wasm.Wast.AST.Operation
open Wasm.Wast.AST.Func

open ByteArray
open Nat

namespace Wasm.Bytes

def magic : ByteArray := ByteArray.mk #[0, 0x61, 0x73, 0x6d]

def version : ByteArray := ByteArray.mk #[1, 0, 0, 0]

def b (x : UInt8) : ByteArray :=
  ByteArray.mk #[x]

def b0 := ByteArray.mk #[]

def flatten (xs : List ByteArray) : ByteArray :=
  xs.foldl Append.append b0

def ttoi (x : Type') : UInt8 :=
  match x with
  | .i 32 => 0x7f
  | .i 64 => 0x7e
  | .f 32 => 0x7d
  | .f 64 => 0x7c

def lindex (bss : ByteArray) : ByteArray :=
  uLeb128 bss.data.size ++ bss

def vectorise (bs : List ByteArray) : ByteArray :=
  uLeb128 bs.length ++ flatten bs

def mkVecM (xs : List α) (xtobs : α → m ByteArray) [Monad m] : m ByteArray :=
  vectorise <$> xs.mapM xtobs

def mkVec (xs : List α) (xtobs : α → ByteArray) : ByteArray :=
  mkVecM (m := Id) xs xtobs

def mkIndexedVecM (xs : List (Nat × α))
                  (xtobs : α → m ByteArray) [Monad m] : m ByteArray :=
  let xbs := xs.mapM fun (idx, x) => (uLeb128 idx ++ ·) <$> xtobs x
  vectorise <$> xbs

def mkIndexedVec (xs : List (Nat × α)) (xtobs : α → ByteArray) : ByteArray :=
  mkIndexedVecM (m := Id) xs xtobs

def null_byte : ByteArray := ByteArray.mk #[0]

-- Enforce that when something is converted to a byte array, it is not empty or not null.
-- If it isn't, finally run the first argument function on it.
def enf (g : ByteArray → ByteArray) (f : α → ByteArray) (x : α) : ByteArray :=
  match f x with
  | ⟨ #[] ⟩ => b0
  | ⟨ #[0] ⟩ => b0
  | y => g y

def mkStr (x : String) : ByteArray :=
  uLeb128 x.length ++ x.toUTF8

abbrev FuncIds := List (Nat × String)
abbrev FTypes := List FunctionType
abbrev Locals := List (Nat × Local)
abbrev Globals := List (Nat × Global)
abbrev BlockLabels := List (Option String)

abbrev ExtractM := ReaderT FuncIds $ ReaderT FTypes $ ReaderT Globals $ ReaderT Locals
                 $ StateM BlockLabels

def push : Option String → ExtractM PUnit := fun x => do set $ x :: (←get)

def eapp : ByteArray → ExtractM ByteArray → ExtractM ByteArray :=
  Applicative.liftA₂ Append.append ∘ pure


instance : Append (ExtractM ByteArray) := ⟨Applicative.liftA₂ Append.append⟩
instance : HAppend ByteArray (ExtractM ByteArray) (ExtractM ByteArray) := ⟨eapp⟩
instance : HAppend (ExtractM ByteArray) ByteArray (ExtractM ByteArray) where
  hAppend eb b := eb ++ pure b

def readFIds  : ExtractM FuncIds   := readThe FuncIds
def readFTypes  : ExtractM FTypes  := readThe FTypes
def readLocals  : ExtractM Locals  := readThe Locals
def readGlobals : ExtractM Globals := readThe Globals

/-- Index locals of a function. If a function uses a type reference,
we have to consider the amount of parameters in that type, but
their identifiers aren't encoded in the name section nor propagated
to the operations part, so we strip the ids. -/
def indexLocals (f : Func) (ftypes : FTypes) : Locals :=
  let idxParams := match f.ftype with
  | .inr (params, _) => params.enum
  | .inl tid => match fetchFType ftypes tid with
    | .some ft =>
      let stripped := ft.ins.map fun p => {p with name := .none}
      stripped.enum
    | .none => sorry
  let idxLocals := f.locals.enumFrom idxParams.length
  idxParams ++ idxLocals

def indexIdentifiedLocals (f : Func) (ftypes : FTypes) : Locals :=
  let onlyIDed := List.filter (·.2.name.isSome)
  onlyIDed $ indexLocals f ftypes

def indexFuncs (fs : List Func) : List (Nat × Func) := fs.enum

def indexIdentifiedFuncs (fs : List Func) : List (Nat × Func) :=
  let onlyIDed := List.filter (·.2.name.isSome)
  onlyIDed fs.enum

def indexFuncsWithIdentifiedLocals (fs : List Func) (ftypes : FTypes)
  : List (Nat × Locals) :=
  (fs.map fun f => indexIdentifiedLocals f ftypes).enum.filter (!·.2.isEmpty)

def indexIdentifiedGlobals (gs : List Global) : Globals :=
  let onlyIDed := List.filter (·.2.name.isSome)
  onlyIDed gs.enum

-- This makes me cry in pain, but I don't see any way to cut out this pre-pass
-- in this architecture.
-- TODO: lens lib? 🥺
private partial def traverseOp : Operation → List FunctionType
  | .block _ ps ts ops =>
    let fts := (ops.map traverseOp).join
    if !ps.isEmpty || !ts.length ≤ 1
      then mkFunctionType ps ts :: fts
      else fts
  | .loop _ ps ts ops =>
    let fts := (ops.map traverseOp).join
    if !ps.isEmpty || !ts.length ≤ 1
      then mkFunctionType ps ts :: fts
      else fts
  | .if _ ps ts thens elses =>
    let bts := if !ps.isEmpty || !ts.length ≤ 1
      then [mkFunctionType ps ts]
      else []
    let bth := thens.map traverseOp
    let belse := elses.map traverseOp
    bts ++ bth.join ++ belse.join
  | _ => []

/-- Extract a 'function type' construct. -/
def extractFunctionType (ft : FunctionType) : ByteArray :=
  let header := b 0x60
  let params := mkVec ft.ins (b ∘ ttoi ∘ Local.type)
  let result := mkVec ft.outs (b ∘ ttoi)
  header ++ params ++ result

/-- Collect `FunctionType`s of structured control instructions of a `Func`. -/
def collectFuncBlockTypes (f : Func) : FTypes :=
  f.ops.map traverseOp |>.join

/-- Collect all `FunctionType`s from a `Func`, including blocktypes.-/
def collectFuncAllTypes (f : Func) : FTypes :=
  match f.ftype with
  | .inl _ => collectFuncBlockTypes f
  | .inr (params, res) => ⟨.none, params, res⟩ :: collectFuncBlockTypes f

-- TODO: maybe calculate the opcodes instead of having lots of lookup subtables?
-- def extractIBinOp (α : Type') (offset : UInt8)
def extractEqz (α : Type') : ByteArray :=
  b $ match α with
  | .i 32 => 0x45
  | .i 64 => 0x50
  | _ => unreachable!

def extractEq (α : Type') : ByteArray :=
  b $ match α with
  | .i 32 => 0x46
  | .i 64 => 0x51
  | .f 32 => 0x5b
  | .f 64 => 0x61

def extractNe (α : Type') : ByteArray :=
  b $ match α with
  | .i 32 => 0x47
  | .i 64 => 0x52
  | .f 32 => 0x5c
  | .f 64 => 0x62

def extractLt (α : Type') : ByteArray :=
  b $ match α with
  | .f 32 => 0x5d
  | .f 64 => 0x63
  | _ => unreachable!

def extractGt (α : Type') : ByteArray :=
  b $ match α with
  | .f 32 => 0x5e
  | .f 64 => 0x64
  | _ => unreachable!

def extractLe (α : Type') : ByteArray :=
  b $ match α with
  | .f 32 => 0x5f
  | .f 64 => 0x65
  | _ => unreachable!

def extractGe (α : Type') : ByteArray :=
  b $ match α with
  | .f 32 => 0x60
  | .f 64 => 0x66
  | _ => unreachable!

def extractLts (α : Type') : ByteArray :=
  b $ match α with
  | .i 32 => 0x48
  | .i 64 => 0x53
  | _ => unreachable!

def extractLtu (α : Type') : ByteArray :=
  b $ match α with
  | .i 32 => 0x49
  | .i 64 => 0x54
  | _ => unreachable!

def extractGts (α : Type') : ByteArray :=
  b $ match α with
  | .i 32 => 0x4a
  | .i 64 => 0x55
  | _ => unreachable!

def extractGtu (α : Type') : ByteArray :=
  b $ match α with
  | .i 32 => 0x4b
  | .i 64 => 0x56
  | _ => unreachable!

def extractLes (α : Type') : ByteArray :=
  b $ match α with
  | .i 32 => 0x4c
  | .i 64 => 0x57
  | _ => unreachable!

def extractLeu (α : Type') : ByteArray :=
  b $ match α with
  | .i 32 => 0x4d
  | .i 64 => 0x58
  | _ => unreachable!

def extractGes (α : Type') : ByteArray :=
  b $ match α with
  | .i 32 => 0x4e
  | .i 64 => 0x59
  | _ => unreachable!

def extractGeu (α : Type') : ByteArray :=
  b $ match α with
  | .i 32 => 0x4f
  | .i 64 => 0x5a
  | _ => unreachable!

def extractClz (α : Type') : ByteArray :=
  b $ match α with
  | .i 32 => 0x67
  | .i 64 => 0x79
  | _ => unreachable!

def extractCtz (α : Type') : ByteArray :=
  b $ match α with
  | .i 32 => 0x68
  | .i 64 => 0x7a
  | _ => unreachable!

def extractPopcnt (α : Type') : ByteArray :=
  b $ match α with
  | .i 32 => 0x69
  | .i 64 => 0x7b
  | _ => unreachable!

def extractAdd (α : Type') : ByteArray :=
  b $ match α with
  | .i 32 => 0x6a
  | .i 64 => 0x7c
  | .f 32 => 0x92
  | .f 64 => 0xa0

def extractSub (α : Type') : ByteArray :=
  b $ match α with
  | .i 32 => 0x6b
  | .i 64 => 0x7d
  | .f 32 => 0x93
  | .f 64 => 0xa1

def extractMul (α : Type') : ByteArray :=
  b $ match α with
  | .i 32 => 0x6c
  | .i 64 => 0x7e
  | .f 32 => 0x94
  | .f 64 => 0xa2

def extractDiv (α : Type') : ByteArray :=
  b $ match α with
  | .f 32 => 0x95
  | .f 64 => 0xa3
  | _ => unreachable!

def extractMin (α : Type') : ByteArray :=
  b $ match α with
  | .f 32 => 0x96
  | .f 64 => 0xa4
  | _ => unreachable!

def extractMax (α : Type') : ByteArray :=
  b $ match α with
  | .f 32 => 0x97
  | .f 64 => 0xa5
  | _ => unreachable!

def extractCopysign (α : Type') : ByteArray :=
  b $ match α with
  | .f 32 => 0x98
  | .f 64 => 0xa6
  | _ => unreachable!

def extractDivS (α : Type') : ByteArray :=
  b $ match α with
  | .i 32 => 0x6d
  | .i 64 => 0x7f
  | _ => unreachable!

def extractDivU (α : Type') : ByteArray :=
  b $ match α with
  | .i 32 => 0x6e
  | .i 64 => 0x80
  | _ => unreachable!

def extractRemS (α : Type') : ByteArray :=
  b $ match α with
  | .i 32 => 0x6f
  | .i 64 => 0x81
  | _ => unreachable!

def extractRemU (α : Type') : ByteArray :=
  b $ match α with
  | .i 32 => 0x70
  | .i 64 => 0x82
  | _ => unreachable!

def extractAnd (α : Type') : ByteArray :=
  b $ match α with
  | .i 32 => 0x71
  | .i 64 => 0x83
  | _ => unreachable!

def extractOr (α : Type') : ByteArray :=
  b $ match α with
  | .i 32 => 0x72
  | .i 64 => 0x84
  | _ => unreachable!

def extractXor (α : Type') : ByteArray :=
  b $ match α with
  | .i 32 => 0x73
  | .i 64 => 0x85
  | _ => unreachable!

def extractShl (α : Type') : ByteArray :=
  b $ match α with
  | .i 32 => 0x74
  | .i 64 => 0x86
  | _ => unreachable!

def extractShrS (α : Type') : ByteArray :=
  b $ match α with
  | .i 32 => 0x75
  | .i 64 => 0x87
  | _ => unreachable!

def extractShrU (α : Type') : ByteArray :=
  b $ match α with
  | .i 32 => 0x76
  | .i 64 => 0x88
  | _ => unreachable!

def extractRotl (α : Type') : ByteArray :=
  b $ match α with
  | .i 32 => 0x77
  | .i 64 => 0x89
  | _ => unreachable!

def extractRotr (α : Type') : ByteArray :=
  b $ match α with
  | .i 32 => 0x78
  | .i 64 => 0x8a
  | _ => unreachable!

def extractLocalLabel : LocalLabel → ExtractM ByteArray
  | .by_index idx => pure $ sLeb128 idx
  | .by_name name => do match (←readLocals).find? (·.2.name = .some name) with
    | .some (idx, _) => pure $ sLeb128 idx
    | .none => sorry

def extractGlobalLabel : GlobalLabel → ExtractM ByteArray
  | .by_index idx => pure $ sLeb128 idx
  | .by_name name => do match (←readGlobals).find? (·.2.name = .some name) with
    | .some (idx, _) => pure $ sLeb128 idx
    | .none => sorry

def extractBlockLabelId : BlockLabelId → ExtractM ByteArray
  | .by_index idx => pure $ sLeb128 idx
  | .by_name name => do match (←get).findIdx? (· = .some name) with
    | .some idx => pure $ sLeb128 idx
    | .none => sorry

def extractFuncId : FuncId → ExtractM ByteArray
  | .by_index idx => pure $ uLeb128 idx
  | .by_name name => do match (←readFIds).find? (·.2 = name) with
    | .some (idx, _) => pure $ sLeb128 idx
    | .none => sorry

def extractBlockType : FunctionType → ExtractM ByteArray
  | ⟨_,[],[]⟩ => pure $ b 0x40
  | ⟨_,[],[t]⟩ => pure $ b (ttoi t)
  | ft => do
      let ftypes ← readFTypes
      let tidx := ftypes.indexOf ft
      pure $ sLeb128 tidx

  -- https://coolbutuseless.github.io/2022/07/29/toy-wasm-interpreter-in-base-r/

partial def extractOp (op : Operation) : ExtractM ByteArray := do
  match op with
  | .unreachable => pure $ b 0x00
  | .nop => pure $ b 0x01
  | .drop => pure $ b 0x1a
  | .const (.i 32) (.i ci) => pure $ b 0x41 ++ sLeb128 ci.val
  | .const (.i 64) (.i ci) => pure $ b 0x42 ++ sLeb128 ci.val
  | .const _ _ => sorry -- TODO: float binary encoding
  | .select .none => pure $ b 0x1b
  | .select (.some t) => pure $ b 0x1c ++ mkVec [t] (b ∘ ttoi)
  | .eqz t => pure $ extractEqz t
  | .eq t => pure $ extractEq t
  | .ne t => pure $ extractNe t
  | .lt_u t => pure $ extractLtu t
  | .lt_s t => pure $ extractLts t
  | .gt_u t => pure $ extractGtu t
  | .gt_s t => pure $ extractGts t
  | .le_u t => pure $ extractLeu t
  | .le_s t => pure $ extractLes t
  | .ge_u t => pure $ extractGeu t
  | .ge_s t => pure $ extractGes t
  | .lt t => pure $ extractLt t
  | .gt t => pure $ extractGt t
  | .le t => pure $ extractLe t
  | .ge t => pure $ extractGe t
  | .clz    t => pure $ extractClz t
  | .ctz    t => pure $ extractCtz t
  | .popcnt t => pure $ extractPopcnt t
  | .add t => pure $ extractAdd t
  | .sub t => pure $ extractSub t
  | .mul t => pure $ extractMul t
  | .div t => pure $ extractDiv t
  | .min t => pure $ extractMin t
  | .max t => pure $ extractMax t
  | .div_s t => pure $ extractDivS t
  | .div_u t => pure $ extractDivU t
  | .rem_s t => pure $ extractRemS t
  | .rem_u t => pure $ extractRemU t
  | .and t => pure $ extractAnd t
  | .or  t => pure $ extractOr  t
  | .xor t => pure $ extractXor t
  | .shl t => pure $ extractShl t
  | .shr_u t => pure $ extractShrU t
  | .shr_s t => pure $ extractShrS t
  | .rotl t => pure $ extractRotl t
  | .rotr t => pure $ extractRotr t
  | .local_get ll => b 0x20 ++ extractLocalLabel ll
  | .local_set ll => b 0x21 ++ extractLocalLabel ll
  | .local_tee ll => b 0x22 ++ extractLocalLabel ll
  | .global_get gl => b 0x23 ++ extractGlobalLabel gl
  | .global_set gl => b 0x24 ++ extractGlobalLabel gl
  | .block id ps ts ops =>
    push id
    let bts := extractBlockType $ mkFunctionType ps ts
    let obs := bts ++ flatten <$> ops.mapM extractOp
    b 0x02 ++ obs ++ b 0x0b
  | .loop id ps ts ops =>
    push id
    let bts := extractBlockType $ mkFunctionType ps ts
    let obs := bts ++ flatten <$> ops.mapM extractOp
    b 0x03 ++ obs ++ b 0x0b
  | .if id ps ts thens elses =>
    push id
    let bts := extractBlockType $ mkFunctionType ps ts
    let bth ← flatten <$> thens.mapM extractOp
    let belse ← if elses.isEmpty then pure b0 else
      b 0x05 ++ flatten <$> elses.mapM extractOp
    b 0x04 ++ bts ++ bth ++ belse ++ b 0x0b
  | .br bl => b 0x0c ++ extractBlockLabelId bl
  | .br_if bl => b 0x0d ++ extractBlockLabelId bl
  | .br_table bls bld =>
    b 0x0e ++ mkVecM bls extractBlockLabelId ++ extractBlockLabelId bld
  | .call fi => b 0x10 ++ extractFuncId fi
  | .return => pure $ b 0x0f

def extractOps (ops : List Operation) : ExtractM ByteArray :=
  flatten <$> ops.mapM extractOp

/-- Take a list and deduplicate it in `O(n²)`, depending only on `BEq`. -/
/- Sadly, we can't use `RBSet` and the like to achieve better performance.
For us, the order in the original list, i.e. the original order of functions
that produce this list, matters, and it's not capturable in a `cmp` function. -/
private def poorMansDeduplicate (xs : List α) [BEq α] : List α :=
  let rec go acc
    | [] => acc.toList
    | x::xs => if acc.contains x then go acc xs else go (acc.push x) xs
  go #[] xs

def typeHeader := b 0x01

def extractTypes (m : Module) : FTypes :=
  poorMansDeduplicate $
    m.types ++ (m.func.map collectFuncAllTypes |> .join)

/- Function section -/

def extractFuncIds (m : Module) (types : FTypes) : ByteArray :=
  if m.func.isEmpty then b0 else
    let getIndex f := match f.ftype with
      | .inl (.by_index idx) => idx
      | .inl (.by_name n) => match types.findIdx? (·.tid = .some n) with
        | .some idx => idx
        | .none => sorry
      | .inr (params, results) => types.indexOf ⟨.none, params, results⟩
    let funcIds := mkVec m.func (uLeb128 ∘ getIndex)
    b 0x03 ++ lindex funcIds

def extractFuncBody (fids : FuncIds) (functypes : FTypes) (gls : Globals)
                    (f : Func)
                    : (ByteArray × BlockLabels) :=
  -- Locals are encoded with counts of subgroups of the same type.
  let localGroups := f.locals.groupBy (fun l1 l2 => l1.type = l2.type)
  let extractCount
    | ls@(l::_) => uLeb128 ls.length ++ b (ttoi l.type)
    | [] => b0
  let locals := mkVec localGroups extractCount

  -- We also return all the previously collected block labels, as we'll
  -- need them in the names section.
  let (obs, bls) := (extractOps f.ops).run fids functypes gls (indexIdentifiedLocals f functypes) []

  -- for each function's code section, we'll add its size after we do
  -- all the other computations.
  -- We need them reversed, as the names section mentions them top-down,
  -- whereas in extracting the func's body we need to break out from the bottom.
  (lindex $ locals ++ obs ++ b 0x0b, bls.reverse)

def extractFuncBodies (m : Module) (functypes : FTypes)
                      : (ByteArray × List BlockLabels) :=
  if m.func.isEmpty then (b0, []) else
    let header := b 0x0a
    let funcIds := m.func.enum.filterMap fun (idx, f) =>
      if let .some id := f.name then .some (idx, id) else .none
    let extractFBwGlobals := extractFuncBody funcIds functypes $
      indexIdentifiedGlobals m.globals
    let (fbs, bls) := List.unzip $ m.func.map extractFBwGlobals
    (header ++ lindex (vectorise fbs), bls)

def modHeader : ByteArray := b 0x00

def extractModIdentifier : Module → ByteArray
| ⟨.none, _, _, _⟩ => b0
| ⟨.some n, _, _, _⟩ => modHeader ++ (lindex $ lindex n.toUTF8)

def funcHeader : ByteArray := b 0x01

def extractFuncIdentifier (f : Func) : ByteArray :=
  if let .some x := f.name then mkStr x else b0

def extractGlobalIdentifier : Global → ByteArray
| ⟨ .none, _, _ ⟩ => b0
| ⟨ .some x, _, _ ⟩ => lindex x.toUTF8

def extractFTypeIdentifier : FunctionType → ByteArray
| ⟨ .none, _, _ ⟩ => b0
| ⟨ .some x, _, _ ⟩ => lindex x.toUTF8

def flattenWithIndices : List ByteArray → ByteArray
  | [] => b0
  | bs => (bs.foldl (fun (acc, n) x => match x.data with
    | #[] => (acc, n)
    | _x => ((acc ++ uLeb128 n ++ x), n + 1)) (b0, 0)).1

-- Same as extractModIdentifier, but maps a list of functions into a length-prefixed wasm array.
def extractFuncIdentifiers (fs : List Func) : ByteArray :=
  let nfs := indexIdentifiedFuncs fs
  if nfs.isEmpty then b0 else
    let fbs := mkIndexedVec nfs extractFuncIdentifier
    funcHeader ++ lindex fbs

-- Very similar to extractFuncIdentifiers, but for globals.
def extractGlobalIdentifiers (gs : List Global) : ByteArray :=
  let ngs := indexIdentifiedGlobals gs
  if ngs.isEmpty then b0 else
    let gbs := mkIndexedVec ngs extractGlobalIdentifier
    b 0x07 ++ lindex gbs

/-
                       ___________________________________________________
                      /                                                   \
                     |                                                    |
                     |            (_) __ _  ___| | ____ _| |              |
                     |            | |/ _` |/ __| |/ / _` | |              |
                     |            | | (_| | (__|   < (_| | |              |
                     |           _/ |\__,_|\___|_|\_\__,_|_|              |
                     |          |__/                                      |
                     |                                                    |
                     |                         _   _  __ _          _     |
                     |            ___ ___ _ __| |_(_)/ _(_) ___  __| |    |
                     |           / __/ _ \ '__| __| | |_| |/ _ \/ _` |    |
                     |          | (_|  __/ |  | |_| |  _| |  __/ (_| |    |
                     |           \___\___|_|   \__|_|_| |_|\___|\__,_|    |
                     |                                                    |
        _            ,_     ______________________________________________.
       / \      _-'    |   /
     _/|  \-''- _ /    |  /
__-' { |          \    | /
    /             \    |/
    /       "o.  |o }
    |            \ ;                 TODO: generalise
                  ',                    wasm maps
       \_         __\               and indirect maps
         ''-_    \.//
           / '-____'
          /
        _'
      _-

-/

def extractGlobalType : GlobalType → ByteArray
  | ⟨mut?, t⟩ => b (ttoi t) ++ b (if mut? then 0x01 else 0x00)

def extractGlobal (g : Global) : ByteArray :=
  let egt := extractGlobalType g.type
  let einit := match g.init with -- some copy paste to avoid passing locals
  | .const (.i 32) (.i ci) => b 0x41 ++ sLeb128 ci.val
  | .const (.i 64) (.i ci) => b 0x42 ++ sLeb128 ci.val
  | _ => unreachable! -- TODO: upon supporting imports, add that global.get case
  egt ++ einit ++ b 0x0b

def extractGlobals : List Global → ByteArray :=
  enf (b 0x06 ++ lindex ·) (mkVec · extractGlobal)

def encodeLocal (l : Nat × Local) : ByteArray :=
  match l.2.name with
  | .some n => uLeb128 l.1 ++ mkStr n
  | .none   => uLeb128 l.1 -- TODO: check logic

def encodeFunc (f : (Nat × Locals)) : ByteArray :=
  uLeb128 f.1 ++ mkVec f.2 encodeLocal

def extractLocalIdentifiers (fs : List Func) (ftypes : FTypes)
                            : ByteArray :=
  let subsection_header := b 0x02
  let ifs := indexFuncsWithIdentifiedLocals fs ftypes
  if !ifs.isEmpty then
    subsection_header ++ lindex (mkVec ifs encodeFunc)
  else
    b0

def extractBlockIdentifiers (blockLabels : List BlockLabels) : ByteArray :=
  /- num of funcs w/ block labels
      func index (overall) | num of block labels in this func
        index of block instruction | str w/ size
   -/
  -- filter out functions that don't have named blocks
  let subsection_header := b 0x03
  let labelousFuncs := blockLabels.enum.filter (·.2.any (·.isSome))
  if !labelousFuncs.isEmpty then
    let onlyNamed bls := bls.enum.filterMap fun (idx, bs) => (idx, ·) <$> bs
    let encodeOneFuncsBLs bls := mkIndexedVec (onlyNamed bls) mkStr
    let ids := mkIndexedVec labelousFuncs encodeOneFuncsBLs
    subsection_header ++ lindex ids
  else
    b0

def extractFTypeIdentifiers (ftypes : List FunctionType) : ByteArray :=
  let subsection_header := b 0x04
  let labelousFTypes := ftypes.enum.filter (·.2.tid.isSome)
  if labelousFTypes.isEmpty then b0 else
    let fts := mkIndexedVec labelousFTypes extractFTypeIdentifier
    subsection_header ++ lindex fts

def extractIdentifiers (m : Module) (blockLabels : List BlockLabels) : ByteArray :=
  let header := b 0x00
  let nameSectionStarts := lindex "name".toUTF8
  let modIdentifier := extractModIdentifier m
  let funcIdentifiers := extractFuncIdentifiers m.func
  let locIdentifiers := extractLocalIdentifiers m.func m.types
  let blockIdentifiers := extractBlockIdentifiers blockLabels
  let ftypeIdentifiers := extractFTypeIdentifiers m.types
  let globalIdentifiers := extractGlobalIdentifiers m.globals
  let ids := modIdentifier ++ funcIdentifiers ++ locIdentifiers
    ++ blockIdentifiers ++ ftypeIdentifiers ++ globalIdentifiers
  if ids.size > 0 then header ++ lindex (nameSectionStarts ++ ids) else b0

def extractExports (m : Module) : ByteArray :=
  let exports := m.func.enum.filter (·.2.export_.isSome)
  if !exports.isEmpty then
    let header := b 0x07
    let extractExport | (idx, f) => match f.export_ with
      | .some x => mkStr x ++ b 0x00 ++ uLeb128 idx
      | .none => b0
    header ++ lindex (mkVec exports extractExport)
  else
    b0

def mtob (m : Module) : ByteArray :=
  -- we extract deduplicated types here since we need it to
  -- look up correct function indices in the funcids section
  let types := extractTypes m
  let typeSection := if types.isEmpty then b0 else
    typeHeader ++ lindex (vectorise $ types.map extractFunctionType)
  let (funcBodies, blockLabels) := extractFuncBodies m types
  magic ++
  version ++
  typeSection ++
  (extractFuncIds m types) ++
  (extractGlobals m.globals) ++
  (extractExports m) ++
  (funcBodies) ++
  (extractIdentifiers m blockLabels)
