import Wasm
import Wasm.Wast.Code
import Wasm.Wast.Expr
import Wasm.Wast.Name
import Wasm.Wast.Num

import Megaparsec.Parsec

open Wasm.Wast.Code
open Wasm.Wast.Code.Operation
open Wasm.Wast.Expr
open Wasm.Wast.Name
open Wasm.Wast.Num
open Num.Digit
open Num.Nat
open Num.Int
open Num.Float

open Megaparsec.Parsec

def sameName (_n₁ : Option $ Name x) (_n₂ : Option $ Name x) : Option (Name "kek") := mkName "kek"
#eval sameName (mkName "lol") (mkName "lol")
-- #eval sameName (mkName "lol") (mkName "kek")

def main : IO Unit := do

  IO.println "(11) WASM demo coming soon."

  IO.println s!"Digits parse rather efficiently! And now, ergonomically!"
  let d11 : Digit 'b' := {}
  IO.println s!"{(d11 : Nat)} == 11" -- We can 'Coe'rce!

  IO.println s!"We have numbers!"
  let n222 : Option $ Nat' "22_2_2" := mkNat' "22_2_2"
  let nHd : Option $ Nat' "Herder" := mkNat' "Herder"

  match n222 with
  | .some sn222 => IO.println s!"{(sn222 : Nat)} == 2222"
  | .none => IO.println "/_!_\\ BUG IN Nat' \"22\" clause /_!_\\"

  match nHd with
  | .some _ => IO.println "/_!_\\ BUG IN Nat' \"Herder\" clause /_!_\\"
  | .none => IO.println s!":thumbs_up:"

  IO.println s!"Let's try signed integers?"
  let ints := "-50_0"
  match mkInt' ints with
  | .some int => IO.println s!"{ints} == {(int : Int)}"
  | .none => IO.println s!"/_!_\\ BUG IN Int' {ints} clause"

  IO.println s!"Heck, we even have floats!"
  let n222d22e2 : Option $ Float' "22_2.2_2E+2" := mkFloat' "22_2.2_2E+2"
  match n222d22e2 with
  | .some sn222d22e2 => IO.println s!"My little number: Coe is magic. 222.22e2 == {(sn222d22e2 : Float) + 0.0} == 22222.0"
  | .none => IO.println "/_!_\\ BUG IN Float' \"22_2.2_2E+2\" clause /_!_\\"

  IO.println s!"Negative exponent and significand work, too!"
  let fls := "-123.45e-2"
  match mkFloat' fls with
  | .some fl => IO.println s!"{fls} == {(fl : Float)} == -1.2345"
  | .none => IO.println s!"Oh no, bug in {fls} parsing!"

  IO.println "* * *"
  IO.println "f32 is represented as:"
  void $ parseTestP Type'.typeP "f32"
  IO.println "* * *"

  IO.println "* * *"
  IO.println "i32.const 42 is represented as:"
  void $ parseTestP i32P "i32.const 42"
  IO.println "* * *"

  IO.println "* * *"
  IO.println "(i32.add (i32.const 42)) is represented as:"
  void $ parseTestP addP "(i32.add (i32.const 42))"
  IO.println "* * *"

  let mut x := 0
  x := 1
  IO.println s!"Thanks for using Webassembly with Lean, you're #{x}!"

  pure ()
