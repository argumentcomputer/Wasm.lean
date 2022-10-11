import Wasm
import Wasm.Wast.Expr

open  Wasm.Wast.Expr

def sameName (_n₁ : Option $ Name x) (_n₂ : Option $ Name x) : Option (Name "kek") := mkName "kek"
#eval sameName (mkName "lol") (mkName "lol")
-- #eval sameName (mkName "lol") (mkName "kek")

def main : IO Unit := do
  IO.println "(8) WASM demo coming soon."

  IO.println "Let's count the dots (should be two for constructing and zero for extracting Nat with .g)!"
  let x23 : Xf 23 := {}
  let x23' : Xf 23 := {}
  let x55 : Xf 55 := {}
  IO.println s!"So... We actually parsed only twice, but we've got three values: {x23.g x23.y}, {x23'.g x23.y}, {x55.g x55.y}"
  IO.println s!"Over and over again: {x23.g x23.y}, {x23'.g x23.y}, {x55.g x55.y}"
  IO.println s!"And again: {x23.g x23.y}, {x23'.g x23.y}, {x55.g x55.y}"

  IO.println "Also, Lean is known to be a technology from the future:"
  let xx23 : X 23 := {}
  IO.println s!"Such reduction: {xx23.g xx23.y}"
  IO.println s!"Much techmology: {xx23.g xx23.y}"
  IO.println s!"Wow: {xx23.g xx23.y}"

  pure ()
