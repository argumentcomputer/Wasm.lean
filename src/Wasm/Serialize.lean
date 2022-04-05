import Wasm.Serialize.Putter



/-
Serialize a Type to Wasm bytecode.
-/
class Serialize (T : Type) where
  put {M : Type → Type} [Monad M] [MonadExcept E M] (t : T) : M Unit
  get {M : Type → Type} [Monad M] [MonadExcept E M] : M T
