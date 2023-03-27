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

def run_wasm (m : Module) : Int := Id.run $ do
  let un₀ := NumUniT.i $ ConstInt.mk 32 0
  let se₀ := StackEntry.num un₀
  let store := mkStore m
  -- Use function #0
  let eres := run store 0 $ Stack.mk [se₀, se₀]
  match eres with
  | .ok σ₂ => match σ₂.es with
    | x :: _ => match x with
      | .num un => match un with
        | .i i => i.val
    | _ => (-4 : Int)
  | _ => (-5 : Int)
