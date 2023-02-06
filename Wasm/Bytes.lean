import Wasm.Wast.AST
import Wasm.Wast.Code
import YatimaStdLib
import Wasm.Leb128

open Wasm.Leb128
open Wasm.Wast.Code
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

def copp [Append α] : α → α → α :=
  fun a x => x ++ a

def totalLength (bss : List ByteArray) : Nat :=
  bss.foldl (fun acc x => acc + x.data.size) 0

def lindex (bss : ByteArray) : ByteArray :=
  uLeb128 bss.data.size ++ bss

-- TODO: Refactor completely and support locals!
def extractTypes (m : Module) : ByteArray :=
  let sigs := m.func.map $ fun x =>
    let params := x.params.map $ (b ∘ ttoi ∘ fun x => x.type)
    -- TODO: check if we support > 255 params. Do the same for each length and size entries!
    let header := b 0x60 ++ uLeb128 params.length
    let res := params.foldl Append.append header
    res ++ (match x.results with -- TODO: test multi-result functions
    | List.nil => b 0x00
    | ts => b 0x7b ++ uLeb128 ts.length ++ flatten (ts.map $ b ∘ ttoi)
    )
  sigs.foldl
    Append.append $
      b 0x01 ++ uLeb128 (1 + totalLength sigs) ++ uLeb128 sigs.length

/- Function section -/
def extractFuncIds (m : Module) : ByteArray :=
  let funs :=
    b m.func.length.toUInt8 ++
    m.func.foldl (fun acc _x => (acc ++ (b ∘ Nat.toUInt8) acc.data.size)) b0
  b 0x03 ++ uLeb128 funs.data.size ++ funs

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

mutual
  -- https://coolbutuseless.github.io/2022/07/29/toy-wasm-interpreter-in-base-r/
  partial def extractGet' (x : Get') : ByteArray :=
    match x with
    | .from_stack => b0
    | .from_operation o => extractOp o
    -- TODO: handle locals
    | _ => sorry

  partial def extractOp (x : Operation) : ByteArray :=
    match x with
    | .nop => b 0x01
    | .drop => b 0x1a
    -- TODO: signed consts exist??? We should check the spec carefully.
    | .const (.i 32) (.i ci) => b 0x41 ++ sLeb128 ci.val
    | .const (.i 64) (.i ci) => b 0x42 ++ sLeb128 ci.val
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
    | .block ts ops =>
      let bts := flatten $ ts.map (b ∘ ttoi)
      let obs := bts ++ uLeb128 ops.length ++ flatten (ops.map extractOp)
      b 0x02 ++ bts ++ lindex obs ++ b 0x0b
    | .loop ts ops =>
      let bts := flatten $ ts.map (b ∘ ttoi)
      let obs := bts ++ uLeb128 ops.length ++ flatten (ops.map extractOp)
      b 0x03 ++ bts ++ lindex obs ++ b 0x0b
    | .if ts thens elses =>
      let bts := flatten $ ts.map (b ∘ ttoi)
      let bth := uLeb128 thens.length ++ flatten (thens.map extractOp)
      let belse := if elses.isEmpty then b0
        else
          let bel := uLeb128 elses.length ++ flatten (elses.map extractOp)
          b 0x05 ++ lindex bel
      b 0x04 ++ bts ++ lindex (bth ++ belse) ++ b 0x0b
    | .br li => b 0x0c ++ sLeb128 li
    | .br_if li => b 0x0d ++ sLeb128 li


end

def extractOps (ops : List Operation) : List ByteArray :=
  ops.map extractOp

def extractFuncs (fs : List Func) : ByteArray :=
  let header := b 0x0a -- ← here we'll add the whole size of the section.
  let fbs := flatten $ fs.map (fun x =>
    -- ← now for each function's code section, we'll add its size after we do all the other
    --   computations.

    -- TODO: handle Locals!
    -- let locals := b 0x0
    let locals := b 0x00

    let obs := (flatten ∘ extractOps) x.ops

    lindex $ locals ++ obs ++ b 0x0b
  )
  header ++ (lindex $ uLeb128 fs.length ++ fbs)

-- TODO
def extractModName (_ : Module) : ByteArray := b0
-- TODO
def extractFuncNames (_ : List Func) : ByteArray := b0

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
def indexNamedLocals (f : Func) : List (Nat × Local) :=
  let go (acc : (Nat × List (Nat × Local))) (x : Local) :=
    let i := acc.1
    if x.name.isSome then (i + 1, (i, x) :: acc.2) else (i + 1, acc.2)
  let indexed_params := f.params.foldl go (0, [])
  let params := indexed_params.2.reverse
  let locals_proper := (f.locals.foldl go (indexed_params.1, [])).2.reverse
  params ++ locals_proper

def indexFunctionsWithNamedLocals (fs : List Func)
  : List (Nat × List (Nat × Local)) :=
  let go (acc : (Nat × List (Nat × List (Nat × Local)))) (x : Func) :=
    let i := acc.1
    let ls := indexNamedLocals x
    if !ls.isEmpty then (i + 1, (i, ls) :: acc.2) else (i + 1, acc.2)
  (fs.foldl go (0, [])).2.reverse

def indexFuncs (fs : List Func) : List (Nat × Func) :=
  let go (acc : List (Nat × Func)) (f : Func) :=
    match acc with
    | [] => [(0, f)]
    | j :: _ => (j.1, f) :: acc
  (fs.foldl go []).reverse

def encodeLocal (l : Nat × Local) : ByteArray :=
  match l.2.name with
  | .some n => uLeb128 l.1 ++ uLeb128 n.length ++ n.toUTF8
  | .none   => uLeb128 l.1 -- TODO: check logic

def encodeFunc (f : (Nat × List (Nat × Local))) : ByteArray :=
  let locals := f.2.map encodeLocal
  uLeb128 f.1 ++ uLeb128 f.2.length ++ flatten locals

def extractLocalNames (fs : List Func) : ByteArray :=
  let subsection_header := b 0x02
  let ifs := (indexFunctionsWithNamedLocals fs).map encodeFunc
  if !ifs.isEmpty then
    subsection_header ++ (lindex $ uLeb128 ifs.length ++ flatten ifs)
  else
    b0

def extractNames (m : Module) : ByteArray :=
  let header := b 0x00
  -- let name := ByteArray.mk #[0x6e, 0x61, 0x6d, 0x65] -- == literal "name"
  let name := "name".toUTF8
  let modName := extractModName m
  let funcNames := extractFuncNames m.func
  let locNames := extractLocalNames m.func
  if (modName.size > 0 || funcNames.size > 0 || locNames.size > 0) then
    header ++ (lindex $ (lindex name) ++ modName ++ funcNames ++ locNames)
  else
    b0

def mkVec (xs : List α) (xtobs : α → ByteArray) : ByteArray :=
  let n := xs.length
  let bs := flatten $ xs.map xtobs
  uLeb128 n ++ bs

def nMkStr (x : String) : ByteArray :=
  uLeb128 x.length ++ x.toUTF8

def extractExports (m : Module) : ByteArray :=
  let exports := m.func.filter (fun f => Option.toBool f.export_)
  if !exports.isEmpty then
    let header := b 0x07
    let extractExport := fun f => match f.2.export_ with
      | .some x => nMkStr x ++ b 0x00 ++ uLeb128 f.1
      | .none => b0
    let fs := indexFuncs ∘ m.func.filter $ fun f => Option.toBool f.export_
    header ++ (lindex $ mkVec fs extractExport)
  else
    b0

def mtob (m : Module) : ByteArray :=
  magic ++
  version ++
  (extractTypes m) ++
  (extractFuncIds m) ++
  (extractExports m) ++
  (extractFuncs m.func) ++
  (extractNames m)
