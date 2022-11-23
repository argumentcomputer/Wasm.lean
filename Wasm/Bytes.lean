import Wasm.Wast.Code
import YatimaStdLib
import Wasm.Leb128

open Wasm.Leb128
open Wasm.Wast.Code.Module
open Wasm.Wast.Code.Type'
open Wasm.Wast.Code.Local
open Wasm.Wast.Code.Operation
open Wasm.Wast.Code.Func
open Wasm.Wast.Code.Get

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
    let params := x.params.map $ (b ∘ ttoi ∘ localToType)
    -- TODO: check if we support > 255 params. Do the same for each length and size entries!
    let header := ByteArray.mk #[0x60, params.length.toUInt8]
    let res := params.foldl Append.append header
    res ++ (match x.result with --TODO: figure out and support multi-output functions
    | .none => b 0x00
    | .some t => ByteArray.mk #[1, ttoi t]
    )
  sigs.foldl
    Append.append $
    ByteArray.mk #[0x01, 1 + (Nat.toUInt8 ∘ totalLength) sigs, sigs.length.toUInt8]

def extractFuncIds (m : Module) : ByteArray :=
  let funs :=
    b m.func.length.toUInt8 ++
    m.func.foldl (fun acc _x => ((b ∘ Nat.toUInt8) acc.data.size) ++ acc) b0
  b 0x03 ++ uLeb128 funs.data.size ++ funs

mutual
  -- https://coolbutuseless.github.io/2022/07/29/toy-wasm-interpreter-in-base-r/
  partial def extractGet' (x : Get') : ByteArray :=
    match x with
    | .from_stack => b0
    | .from_operation o => extractOp o
    -- TODO: signed consts exist??? We should check the spec carefully.
    | .i_const i => ByteArray.mk #[0x41] ++ sLeb128 i.val
    -- TODO: handle locals
    | _ => b0

  partial def extractAdd (α : Type') : ByteArray :=
    b $ match α with
    | .i 32 => 0x6a
    | .i 64 => 0x7c
    | .f 32 => 0x92
    | .f 64 => 0xa0

  partial def extractOp (x : Operation) : ByteArray :=
    match x with
    | .add a => match a with
      | .add t g1 g2 =>
        -- Enter stackman
        extractGet' g1 ++ extractGet' g2 ++ extractAdd t
end

def extractOps (ops : List Operation) : List ByteArray :=
  ops.map extractOp

def extractFuncs (fs : List Func) : ByteArray :=
  let header := b 0x0a -- ← here we'll add the whole size of the section.
  let fn := b $ fs.length.toUInt8
  let fbs := flatten $ fs.map (fun x =>
    -- ← now for each function's code section, we'll add its size after we do all the other
    --   computations.

    -- TODO: handle Locals!
    let locals := b 0x0

    let obs := (flatten ∘ extractOps) x.ops

    lindex $ locals ++ obs ++ b 0x0b
  )
  header ++ (lindex $ fn ++ fbs)

-- TODO
def extractModName (_ : Module) := b0
-- TODO
def extractFuncNames (_ : List Func) := b0

/-
                       ___________________________________________________
                      /                                                   \
   _            _    |    _                                               |
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
def indexNamedLocals (f : Func) : List (Nat × LocalName) :=
  let go (acc : (Nat × List (Nat × LocalName))) (x : Local) :=
    let i := acc.1
    match x with
    | .name y => (i + 1, (i, y) :: acc.2)
    | _ => (i + 1, acc.2)
  let indexed_params := f.params.foldl go (0, [])
  let params := indexed_params.2.reverse
  let locals_proper := (f.locals.foldl go (indexed_params.1, [])).2.reverse
  params ++ locals_proper

def indexFunctionsWithNamedLocals (fs : List Func) : List (Nat × List (Nat × LocalName)) :=
  let go (acc : (Nat × List (Nat × List (Nat × LocalName)))) (x : Func) :=
    let i := acc.1
    let ls := indexNamedLocals x
    if ls.length > 0 then
      (i + 1, (i, ls) :: acc.2)
    else
      (i + 1, acc.2)
  (fs.foldl go (0, [])).2.reverse

def encodeLocal (l : Nat × LocalName) : ByteArray :=
  uLeb128 l.1 ++ uLeb128 l.2.name.length ++ l.2.name.toUTF8

def encodeFunc (f : (Nat × List (Nat × LocalName))) : ByteArray :=
  let locals := f.2.map encodeLocal
  uLeb128 f.1 ++ uLeb128 f.2.length ++ flatten locals

def extractLocalNames (fs : List Func) : ByteArray :=
  let subsection_header := b 0x02
  let ifs := (indexFunctionsWithNamedLocals fs).map encodeFunc
  subsection_header ++ (lindex $ uLeb128 ifs.length ++ flatten ifs)

def extractNames (m : Module) : ByteArray :=
  let header := b 0x00
  -- let name := ByteArray.mk #[0x6e, 0x61, 0x6d, 0x65] -- == literal "name"
  let name := "name".toUTF8
  let modName := extractModName m
  let funcNames := extractFuncNames m.func
  let locNames := extractLocalNames m.func
  header ++ (lindex $ (lindex name) ++ modName ++ funcNames ++ locNames)

def mtob (m : Module) : ByteArray :=
  magic ++
  version ++
  (extractTypes m) ++
  (extractFuncIds m) ++
  (extractFuncs m.func) ++
  (extractNames m)
