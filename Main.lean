import Wasm
import Wasm.Wast.Expr
import Wasm.Wast.Name
import Wasm.Wast.Num

open  Wasm.Wast.Expr
open  Wasm.Wast.Name
open  Wasm.Wast.Num
open  Num.Digit
open  Num.Nat

def sameName (_n₁ : Option $ Name x) (_n₂ : Option $ Name x) : Option (Name "kek") := mkName "kek"
#eval sameName (mkName "lol") (mkName "lol")
-- #eval sameName (mkName "lol") (mkName "kek")

def main : IO Unit := do

  IO.println "(10) WASM demo coming soon."

  IO.println s!"Digits also parse rather efficiently! And now, ergonomically!"
  let d11 : Digit 'b' := {}
  IO.println s!"{(d11 : Nat)} == 11" -- We can 'Coe'rce!

  IO.println s!"We have numbers!"
  let n22 : Option $ Nat' "22" := mkNat' "22"
  let nHd : Option $ Nat' "Herder" := mkNat' "Herder"

  match n22 with
  | .some sn22 => IO.println s!"{(sn22 : Nat)} == 22"
  | .none => IO.println "/_!_\\ BUG IN Nat' \"22\" clause /_!_\\"

  match nHd with
  | .some _ => IO.println "/_!_\\ BUG IN Nat' \"Herder\" clause /_!_\\"
  | .none => IO.println s!":thumbs_up:"

  pure ()
