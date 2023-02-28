import Wasm.Wast.AST
import Wasm.Wast.Code
import Wasm.Leb128

open Wasm.Leb128
open Wasm.Wast.Code
open Wasm.Wast.AST.Global
open Wasm.Wast.AST.Module
open Wasm.Wast.AST.Type'
open Wasm.Wast.AST.Local
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

-- Currently we don't support type indices.
def extractBlockType (ts : List Type') : ByteArray :=
  if ts.isEmpty then b 0x40 else flatten $ ts.map (b ∘ ttoi)

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

abbrev Locals := List (Nat × Local)
abbrev Globals := List (Nat × Global)

abbrev ExtractM := ReaderT Globals $ ReaderM Locals

def eapp : ByteArray → ExtractM ByteArray → ExtractM ByteArray :=
  Applicative.liftA₂ Append.append ∘ pure


instance : Append (ExtractM ByteArray) := ⟨Applicative.liftA₂ Append.append⟩
instance : HAppend ByteArray (ExtractM ByteArray) (ExtractM ByteArray) := ⟨eapp⟩
instance : HAppend (ExtractM ByteArray) ByteArray (ExtractM ByteArray) where
  hAppend eb b := eb ++ pure b

def readLocals : ExtractM Locals := readThe Locals
def readGlobals : ExtractM Globals := readThe Globals

def indexLocals (f : Func) : Locals :=
  let idxParams := f.params.enum
  let idxLocals := f.locals.enumFrom f.params.length
  idxParams ++ idxLocals

def indexIdentifiedLocals (f : Func) : Locals :=
  let onlyIDed := List.filter (·.2.name.isSome)
  onlyIDed $ indexLocals f

def indexFuncs (fs : List Func) : List (Nat × Func) := fs.enum

def indexFuncsWithIdentifiedLocals (fs : List Func)
  : List (Nat × Locals) :=
  (fs.map indexIdentifiedLocals).enum.filter (!·.2.isEmpty)

def indexIdentifiedGlobals (gs : List Global) : Globals :=
  let onlyIDed := List.filter (·.2.name.isSome)
  onlyIDed gs.enum

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

mutual
  -- https://coolbutuseless.github.io/2022/07/29/toy-wasm-interpreter-in-base-r/
  partial def extractGet' (x : Get') : ExtractM ByteArray :=
    match x with
    | .from_stack => pure b0
    | .from_operation o => extractOp o

  partial def extractOp (op : Operation) : ExtractM ByteArray := do
    match op with
    | .nop => pure $ b 0x01
    | .drop => pure $ b 0x1a
    -- TODO: signed consts exist??? We should check the spec carefully.
    | .const (.i 32) (.i ci) => pure $ b 0x41 ++ sLeb128 ci.val
    | .const (.i 64) (.i ci) => pure $ b 0x42 ++ sLeb128 ci.val
    | .const _ _ => sorry -- TODO: float binary encoding
    | .eqz    t g => extractGet' g ++ extractEqz t
    | .eq t g1 g2 => extractGet' g1 ++ extractGet' g2 ++ extractEq t
    | .ne t g1 g2 => extractGet' g1 ++ extractGet' g2 ++ extractNe t
    | .lt_u t g1 g2 => extractGet' g1 ++ extractGet' g2 ++ extractLtu t
    | .lt_s t g1 g2 => extractGet' g1 ++ extractGet' g2 ++ extractLts t
    | .gt_u t g1 g2 => extractGet' g1 ++ extractGet' g2 ++ extractGtu t
    | .gt_s t g1 g2 => extractGet' g1 ++ extractGet' g2 ++ extractGts t
    | .le_u t g1 g2 => extractGet' g1 ++ extractGet' g2 ++ extractLeu t
    | .le_s t g1 g2 => extractGet' g1 ++ extractGet' g2 ++ extractLes t
    | .ge_u t g1 g2 => extractGet' g1 ++ extractGet' g2 ++ extractGeu t
    | .ge_s t g1 g2 => extractGet' g1 ++ extractGet' g2 ++ extractGes t
    | .lt t g1 g2 => extractGet' g1 ++ extractGet' g2 ++ extractLt t
    | .gt t g1 g2 => extractGet' g1 ++ extractGet' g2 ++ extractGt t
    | .le t g1 g2 => extractGet' g1 ++ extractGet' g2 ++ extractLe t
    | .ge t g1 g2 => extractGet' g1 ++ extractGet' g2 ++ extractGe t
    | .clz    t g => extractGet' g ++ extractClz t
    | .ctz    t g => extractGet' g ++ extractCtz t
    | .popcnt t g => extractGet' g ++ extractPopcnt t
    | .add t g1 g2 => extractGet' g1 ++ extractGet' g2 ++ extractAdd t
    | .sub t g1 g2 => extractGet' g1 ++ extractGet' g2 ++ extractSub t
    | .mul t g1 g2 => extractGet' g1 ++ extractGet' g2 ++ extractMul t
    | .div t g1 g2 => extractGet' g1 ++ extractGet' g2 ++ extractDiv t
    | .min t g1 g2 => extractGet' g1 ++ extractGet' g2 ++ extractMin t
    | .max t g1 g2 => extractGet' g1 ++ extractGet' g2 ++ extractMax t
    | .div_s t g1 g2 => extractGet' g1 ++ extractGet' g2 ++ extractDivS t
    | .div_u t g1 g2 => extractGet' g1 ++ extractGet' g2 ++ extractDivU t
    | .rem_s t g1 g2 => extractGet' g1 ++ extractGet' g2 ++ extractRemS t
    | .rem_u t g1 g2 => extractGet' g1 ++ extractGet' g2 ++ extractRemU t
    | .and t g1 g2 => extractGet' g1 ++ extractGet' g2 ++ extractAnd t
    | .or  t g1 g2 => extractGet' g1 ++ extractGet' g2 ++ extractOr  t
    | .xor t g1 g2 => extractGet' g1 ++ extractGet' g2 ++ extractXor t
    | .shl t g1 g2 => extractGet' g1 ++ extractGet' g2 ++ extractShl t
    | .shr_u t g1 g2 => extractGet' g1 ++ extractGet' g2 ++ extractShrU t
    | .shr_s t g1 g2 => extractGet' g1 ++ extractGet' g2 ++ extractShrS t
    | .rotl t g1 g2 => extractGet' g1 ++ extractGet' g2 ++ extractRotl t
    | .rotr t g1 g2 => extractGet' g1 ++ extractGet' g2 ++ extractRotr t
    | .local_get ll => b 0x20 ++ extractLocalLabel ll
    | .local_set ll => b 0x21 ++ extractLocalLabel ll
    | .local_tee ll => b 0x22 ++ extractLocalLabel ll
    | .global_get gl => b 0x23 ++ extractGlobalLabel gl
    | .global_set gl => b 0x24 ++ extractGlobalLabel gl
    | .block ts ops =>
      let bts := extractBlockType ts
      let obs ← bts ++ flatten <$> ops.mapM extractOp
      pure $ b 0x02 ++ obs ++ b 0x0b
    | .loop ts ops =>
      let bts := extractBlockType ts
      let obs ← bts ++ flatten <$> ops.mapM extractOp
      pure $ b 0x03 ++ obs ++ b 0x0b
    | .if ts g thens elses =>
      let bg ← extractGet' g
      let bts := extractBlockType ts
      let bth ← flatten <$> thens.mapM extractOp
      let belse ← if elses.isEmpty then pure b0 else
        b 0x05 ++ flatten <$> elses.mapM extractOp
      pure $ bg ++ b 0x04 ++ bts ++ bth ++ belse ++ b 0x0b
    | .br li => pure $ b 0x0c ++ sLeb128 li
    | .br_if li => pure $ b 0x0d ++ sLeb128 li


end

def extractOps (ops : List Operation) : ExtractM ByteArray :=
  flatten <$> ops.mapM extractOp

def extractFuncTypes (f : Func) : ByteArray :=
  let header := b 0x60
  let params := mkVec f.params (b ∘ ttoi ∘ fun l => l.type)
  let result := mkVec f.results (b ∘ ttoi)
  header ++ params ++ result


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

def extractTypes (m : Module) : List ByteArray :=
  if m.func.isEmpty then [] else
    poorMansDeduplicate $ m.func.map extractFuncTypes

/- Function section -/

def extractFuncIds (m : Module) (types : List ByteArray) : ByteArray :=
  if m.func.isEmpty then b0 else
    let getIndex f := types.indexOf (extractFuncTypes f)
    let funcIds := mkVec m.func (uLeb128 ∘ getIndex)
    b 0x03 ++ lindex funcIds

def extractFuncBody (globals : Globals) (f : Func) : ByteArray :=
  -- Locals are encoded with counts of subgroups of the same type.
  let localGroups := f.locals.groupBy (fun l1 l2 => l1.type = l2.type)
  let extractCount
    | ls@(l::_) => uLeb128 ls.length ++ b (ttoi l.type)
    | [] => b0
  let locals := mkVec localGroups extractCount

  let obs : ByteArray := (extractOps f.ops).run globals (indexIdentifiedLocals f)

  -- for each function's code section, we'll add its size after we do
  -- all the other computations.
  lindex $ locals ++ obs ++ b 0x0b

def extractFuncBodies (m : Module) : ByteArray :=
  if m.func.isEmpty then b0 else
    let header := b 0x0a
    let extractFBwGlobals := extractFuncBody $ indexIdentifiedGlobals m.globals
    header ++ lindex (mkVec m.func extractFBwGlobals)

def modHeader : ByteArray := b 0x00

def extractModIdentifier : Module → ByteArray
| ⟨.none, _, _⟩ => b0
| ⟨.some n, _, _⟩ => modHeader ++ (lindex $ lindex n.toUTF8)

def funcHeader : ByteArray := b 0x01

def extractFuncIdentifier : Func → ByteArray
| ⟨ .none, _, _, _, _, _ ⟩ => b0
| ⟨ .some x, _, _, _, _, _ ⟩ => lindex x.toUTF8

def flattenWithIndices : List ByteArray → ByteArray
  | [] => b0
  | bs => (bs.foldl (fun (acc, n) x => match x.data with
    | #[] => (acc, n)
    | _x => ((acc ++ uLeb128 n ++ x), n + 1)) (b0, 0)).1

-- Same as extractModIdentifier, but maps a list of functions into a length-prefixed wasm array.
def extractFuncIdentifiers (fs : List Func) : ByteArray :=
  let fbs := flattenWithIndices $ fs.map extractFuncIdentifier
  if fbs.size = 0 then
    b0
  else
    funcHeader ++ (lindex $ uLeb128 fs.length ++ fbs)

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

def extractLocalIdentifiers (fs : List Func) : ByteArray :=
  let subsection_header := b 0x02
  let ifs := indexFuncsWithIdentifiedLocals fs
  if !ifs.isEmpty then
    subsection_header ++ lindex (mkVec ifs encodeFunc)
  else
    b0

def extractIdentifiers (m : Module) : ByteArray :=
  let header := b 0x00
  let nameSectionStarts := "name".toUTF8
  let modIdentifier := extractModIdentifier m
  let funcIdentifiers := extractFuncIdentifiers m.func
  let locIdentifiers := extractLocalIdentifiers m.func
  if (modIdentifier.size > 0 || funcIdentifiers.size > 0 || locIdentifiers.size > 0)
  then header ++ (lindex $
    (lindex nameSectionStarts) ++ modIdentifier ++
     funcIdentifiers ++ locIdentifiers)
  else
    b0

def extractExports (m : Module) : ByteArray :=
  let exports := indexFuncs $ m.func.filter (·.export_.isSome)
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
  let typeSection := if m.func.isEmpty then b0 else
    typeHeader ++ lindex (vectorise types)
  magic ++
  version ++
  typeSection ++
  (extractFuncIds m types) ++
  (extractGlobals m.globals) ++
  (extractExports m) ++
  (extractFuncBodies m) ++
  (extractIdentifiers m)
