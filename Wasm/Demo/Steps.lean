import Wasm
import Wasm.Engine
import Wasm.Wast.AST
import Wasm.Wast.Identifier
import Wasm.Wast.Num
import Wasm.Wast.Parser
import Wasm.Bytes
import Wasm.Leb128

import Megaparsec.Parsec

open Wasm.Bytes
open Wasm.Engine
open Wasm.Wast.AST.Func
open Wasm.Wast.AST.Module
open Wasm.Wast.AST.Operation
open Wasm.Wast.Identifier
open Wasm.Wast.Num
open Wasm.Wast.Parser
open Wasm.Leb128

open Num.Digit
open Num.Nat
open Num.Int
open Wasm.Wast.Num.Uni

open Megaparsec.Parsec

def run_wasm (m : Module) : Int :=
  let un₀ := NumUniT.i $ ConstInt.mk 32 0
  let se₀ := StackEntry.StackEntry.num un₀
  match mkStore m with
  | .error _ => -42
  | .ok store =>
  -- Use function #0
    let eres := run store 0 $ Stack.mk [se₀, se₀]
    match eres with
    | .ok σ₂ => match σ₂.2.es with
      | x :: _ => match x with
        | .num un => match un with
          | .i i => i.val
        | _ => (-3 : Int)
      | _ => (-4 : Int)
    | _ => (-5 : Int)
