import Wasm
import Wasm.Wast.Expr
import Wasm.Wast.Name
import Wasm.Wast.Num

open  Wasm.Wast.Expr
open  Wasm.Wast.Name
open  Wasm.Wast.Num
open  Num.Digit
open  Num.Nat
open  Num.Float

def sameName (_n₁ : Option $ Name x) (_n₂ : Option $ Name x) : Option (Name "kek") := mkName "kek"
#eval sameName (mkName "lol") (mkName "lol")
-- #eval sameName (mkName "lol") (mkName "kek")

def main : IO Unit := do

  IO.println "(10) WASM demo coming soon."

  IO.println s!"Digits also parse rather efficiently! And now, ergonomically!"
  let d11 : Digit 'b' := {}
  IO.println s!"{(d11 : Nat)} == 11" -- We can 'Coe'rce!

  IO.println s!"We have numbers!"
  let n222 : Option $ Nat' "22_2_2" := mkNat' "22_2_2"
  let nHd : Option $ Nat' "Herder" := mkNat' "Herder"

  match n222 with
  | .some sn222 => IO.println s!"{(sn222 : Nat)} == 222"
  | .none => IO.println "/_!_\\ BUG IN Nat' \"22\" clause /_!_\\"

  match nHd with
  | .some _ => IO.println "/_!_\\ BUG IN Nat' \"Herder\" clause /_!_\\"
  | .none => IO.println s!":thumbs_up:"

  IO.println s!"Heck, we even have floats!"
  let n222d22e2 : Option $ Float' "22_2.2_2E2" := mkFloat' "22_2.2_2E2"
  match n222d22e2 with
  | .some sn222d22e2 => IO.println s!"My little number: Coe is magic. 222.22e2 == {(sn222d22e2 : Float) + 0.0} == 22222.0"
  | .none => IO.println "/_!_\\ BUG IN Float' \"22_2.2_2E2\" clause /_!_\\"

  pure ()
