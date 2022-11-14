import Wasm.Wast.Code
import YatimaStdLib

open Wasm.Wast.Code.Module
open ByteArray
open Nat

namespace Wasm.Bytes


def mtob (_m : Module) : ByteArray :=
  -- padLeft 0x0061736D.toByteArrayLE 0x0 1
  ByteArray.mk #[0x00] ++ ByteArray.mk #[0x61, 0x73, 0x6d]
