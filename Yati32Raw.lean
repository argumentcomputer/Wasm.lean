import Wasm
import Wasm.Engine
import Wasm.Demo.Steps
import Wasm.Wast.AST
import Wasm.Wast.Identifier
import Wasm.Wast.Num
import Wasm.Wast.Parser
import Wasm.Bytes
import Wasm.Leb128

import Megaparsec.Parsec

open Wasm.Bytes
open Wasm.Engine
open Wasm.Wast.AST.BlockLabel
open Wasm.Wast.AST.Func
open Wasm.Wast.AST.Module
open Wasm.Wast.AST.Local
open Wasm.Wast.AST.Global
open Wasm.Wast.AST.Operation
open Wasm.Wast.Identifier
open Wasm.Wast.Num
open Wasm.Wast.Parser
open Wasm.Leb128

open Num.Digit
open Num.Nat
open Num.Int
-- open Num.Float
open Wasm.Wast.Num.Uni

def erun : Int := Id.run $ do
  -- run_wasm (Module.mk none [(Func.mk (some "main") (some "main") [(Local.mk 0 (some "x") (Type'.i (32 : BitSize))), (Local.mk 1 none (Type'.i (32 : BitSize)))] [(Type'.i (32 : BitSize))] [] [(Operation.add (Add'.add (Type'.i (32 : BitSize)) (Get'.i_const (ConstInt.mk (32 : BitSize) 1819606001)) (Get'.from_operation (Operation.add (Add'.add (Type'.i (32 : BitSize)) (Get'.i_const (ConstInt.mk (32 : BitSize) 30000)) (Get'.i_const (ConstInt.mk (32 : BitSize) 330)))))))])])
  run_wasm (Module.mk none
    [
      (Global.mk "a"
        (GlobalType.mk false (Wasm.Wast.AST.Type'.i (32 : BitSize)))
        (Operation.const
          (Wasm.Wast.AST.Type'.i (32 : BitSize))
          (NumUniT.i (ConstInt.mk (32 : BitSize) 1499550000)))
      ),
      (Global.mk none
        (GlobalType.mk false (Wasm.Wast.AST.Type'.i (32 : BitSize)))
        (Operation.const
          (Wasm.Wast.AST.Type'.i (32 : BitSize))
          (NumUniT.i (ConstInt.mk (32 : BitSize) 17))
        )
      )
    ]
    [(Wasm.Wast.AST.Func.mk "main" "main"
      [
        (Local.mk "x"
          (Wasm.Wast.AST.Type'.i (32 : BitSize))),
          (Local.mk none (Wasm.Wast.AST.Type'.i (32 : BitSize)))
      ]
      [
        (Wasm.Wast.AST.Type'.i (32 : BitSize)),
        (Wasm.Wast.AST.Type'.i (32 : BitSize))
      ] []
      [(Operation.block none []
        [(Wasm.Wast.AST.Type'.i (32 : BitSize))]
        [
          (Operation.const (Wasm.Wast.AST.Type'.i (32 : BitSize)) (NumUniT.i (ConstInt.mk (32 : BitSize) 3))),
          (Operation.br (BlockLabelId.by_index 0)),
          (Operation.const (Wasm.Wast.AST.Type'.i (32 : BitSize)) (NumUniT.i (ConstInt.mk (32 : BitSize) 9))),
          (Operation.add (Wasm.Wast.AST.Type'.i (32 : BitSize)))]),
          (Operation.global_get (GlobalLabel.by_name "a")),
          (Operation.const (Wasm.Wast.AST.Type'.i (32 : BitSize)) (NumUniT.i (ConstInt.mk (32 : BitSize) 9000))),
          (Operation.global_get (GlobalLabel.by_index 1)),
          (Operation.add (Wasm.Wast.AST.Type'.i (32 : BitSize))),
          (Operation.add (Wasm.Wast.AST.Type'.i (32 : BitSize)))])
    ]
  )

def main : IO Unit := do
  IO.println erun
