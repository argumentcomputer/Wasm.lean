import Wasm
import Wasm.Wast.Expr

open  Wasm.Wast.Expr

def sameName (_n₁ : Option $ Name x) (_n₂ : Option $ Name x) : Option (Name "kek") := mkName "kek"
#eval sameName (mkName "lol") (mkName "lol")
-- #eval sameName (mkName "lol") (mkName "kek")

def main : IO Unit := do
  IO.println "(6) WASM demo coming soon."
  IO.println "Let's count the dots (should be two for constructing Nat'' and two for extracting Nat with .val)!"
  let x23  : Nat'' "23" := {doesParse := Exists.intro {} $ by trivial}
  let x23' : Nat'' "23" := {doesParse := Exists.intro {} $ by trivial}
  let x55  : Nat'' "55" := {doesParse := Exists.intro {} $ by trivial}
  IO.println s!"So... We actually parsed only twice, but we've got three values: {x23.val x23.parsed}, {x23'.val x23.parsed}, {x55.val x55.parsed}"
  IO.println s!"We had to parse twice more because `extractNat` evaluates `pr.val`. But after we got these parses, we can keep printing values for free!"
  IO.println s!"Over and over again: {x23.val x23.parsed}, {x23'.val x23.parsed}, {x55.val x55.parsed}"
  IO.println s!"And again: {x23.val x23.parsed}, {x23'.val x23.parsed}, {x55.val x55.parsed}"
  pure ()
