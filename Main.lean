import Wasm
import Wasm.Wast.Expr

open  Wasm.Wast.Expr

def sameName (_n₁ : Option $ Name x) (_n₂ : Option $ Name x) : Option (Name "kek") := mkName "kek"
#eval sameName (mkName "lol") (mkName "lol")
-- #eval sameName (mkName "lol") (mkName "kek")

def main : IO Unit :=
  IO.println "(4) WASM demo coming soon."
