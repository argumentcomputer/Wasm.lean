import Wasm.Wast.Code
import YatimaStdLib

open Wasm.Wast.Code.Module
open ByteArray
open Nat

namespace Wasm.Bytes

def magic : ByteArray := ByteArray.mk #[0, 0x61, 0x73, 0x6d]

def version : ByteArray := ByteArray.mk #[1, 0, 0, 0]

def totalLength (bss : List ByteArray) : Nat :=
  bss.foldl (fun acc x => acc + x.data.size) 0

def extractTypes (m : Module) : ByteArray :=
  let sigs := m.func.map $ fun _x => -- TODO: actually support function decoding
    ByteArray.mk #[0x60, 0x00, 0x00]
    --            func     |     |
    --                  params   |
    --                         result
  sigs.foldl
    (fun acc x => acc ++ x) $
    ByteArray.mk #[0x01, 1 + (Nat.toUInt8 ∘ totalLength) sigs, sigs.length.toUInt8]

def mtob (m : Module) : ByteArray :=
  magic ++
  version ++
  (extractTypes m)
