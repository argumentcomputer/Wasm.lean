import Wasm.Engine
import Wasm.Wast.Code
import Wasm.Wast.Num

import Megaparsec.Parsec

open Wasm.Engine
open Wasm.Wast.Code
open Wasm.Wast.Code.Module
open Wasm.Wast.Num.Uni
open Wasm.Wast.Num.Num.Int

open Megaparsec.Parsec

def go : Int := Id.run $ do
  let un₀ := NumUniT.i $ ConstInt.mk 32 0
  let se₀ := StackEntry.num un₀

  let i := "(module
        (func $main (export \"main\")
            (result i32)

            (i32.add
                (i32.const 1499550000)
                (i32.add (i32.const 9000) (i32.const 17))
            )
        )
    )"

  let o_yati32_mod ← parseP moduleP "." i
  match o_yati32_mod with
  | .error _ => (-1 : Int)
  | .ok m => do
    let store := mkStore m
    let ofid := fidByName store "main"
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
