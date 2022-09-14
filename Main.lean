import Wasm
import Wasm.Wast.Expr

open  Wasm.Wast.Expr

def sameName (_n₁ : Name x) (_n₂ : Name x) : Name "Слава Україні" := {}
#eval sameName ({} : Name "lol") ({} : Name "lol")

def main : IO Unit :=
  IO.println "(3) WASM demo coming soon."
