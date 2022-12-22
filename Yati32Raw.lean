import Wasm.Engine
import Wasm.Wast.Code
import Wasm.Wast.Num
import Wasm.Wast.BitSize

import Megaparsec.Parsec

open Wasm.Engine
open Wasm.Wast.Code
open Wasm.Wast.Code.Module
open Wasm.Wast.Num.Uni
open Wasm.Wast.Num.Num.Int

open Megaparsec.Parsec
open Func
open Type'
open Operation

def go : Int := Id.run $ do
  let un₀ := NumUniT.i $ ConstInt.mk 32 0
  let se₀ := StackEntry.num un₀

  let yati32_mod ← (
    Module.mk none
    [
      (Func.mk none
               (some "main")
               []
               [(Type'.i (32 : BitSize))]
               []
               [
                  (Operation.add (Add'.add (Type'.i (32 : BitSize))
                                 (Get'.i_const (ConstInt.mk (32 : BitSize) 1499550000))
                                 (Get'.from_operation
                                    (Operation.add (Add'.add (Type'.i (32 : BitSize))
                                                   (Get'.i_const (ConstInt.mk (32 : BitSize) 9000))
                                                   (Get'.i_const (ConstInt.mk (32 : BitSize) 17)))))))])])
  let store := mkStore yati32_mod
  let ofid := Option.some 0
  match ofid with
  | .none => (-2 : Int)
  | .some fid =>
    let eres := run store fid $ Stack.mk [se₀, se₀]
    match eres with
    | .ok σ₂ => match σ₂.es with
      | x :: _ => match x with
        | .num un => match un with
          | .i i => i.val
      | _ => (-4 : Int)
    | _ => (-5 : Int)

def main : IO Unit := do
  IO.println go
