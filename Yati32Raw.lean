import Wasm.Demo.Steps
import Wasm.Wast.Num
import Wasm.Wast.Code

open Wasm.Wast.Code
open Wasm.Wast.Code.Module
open Wasm.Wast.Code.Func
open Wasm.Wast.Code.Local
open Wasm.Wast.Code.Type'
open Wasm.Wast.Code.Operation
open Wasm.Wast.Num.Num.Int


def run : Int := Id.run $ do
  run_wasm (Module.mk none [(Func.mk (some "main") (some "main") [(Local.mk 0 (some "x") (Type'.i (32 : BitSize))), (Local.mk 1 none (Type'.i (32 : BitSize)))] [(Type'.i (32 : BitSize))] [] [(Operation.add (Add'.add (Type'.i (32 : BitSize)) (Get'.i_const (ConstInt.mk (32 : BitSize) 1819606001)) (Get'.from_operation (Operation.add (Add'.add (Type'.i (32 : BitSize)) (Get'.i_const (ConstInt.mk (32 : BitSize) 30000)) (Get'.i_const (ConstInt.mk (32 : BitSize) 330)))))))])])

def main : IO Unit := do
  IO.println run
