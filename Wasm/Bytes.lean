import Wasm.Wast.Code
import YatimaStdLib

open Wasm.Wast.Code.Module
open Wasm.Wast.Code.Type'
open Wasm.Wast.Code.Local
open ByteArray
open Nat

namespace Wasm.Bytes

def magic : ByteArray := ByteArray.mk #[0, 0x61, 0x73, 0x6d]

def version : ByteArray := ByteArray.mk #[1, 0, 0, 0]

def b (x : UInt8) : ByteArray :=
  ByteArray.mk #[x]

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

def extractTypes (m : Module) : ByteArray :=
  let sigs := m.func.map $ fun x =>
    let params := x.params.map $ (b ∘ ttoi ∘ localToType)
    let header := ByteArray.mk #[0x60, params.length.toUInt8]
    let res := params.foldl Append.append header
    res ++ b (match x.result with --TODO: figure out and support multi-output functions
    | .none => 0x00
    | .some t => ttoi t
    )
  sigs.foldl
    Append.append $
    ByteArray.mk #[0x01, 1 + (Nat.toUInt8 ∘ totalLength) sigs, sigs.length.toUInt8]

def mtob (m : Module) : ByteArray :=
  magic ++
  version ++
  (extractTypes m)
