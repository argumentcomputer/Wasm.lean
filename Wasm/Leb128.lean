import YatimaStdLib

namespace Wasm.Leb128

def itob (x : Nat) (endianness : Endian := .big) : ByteArray :=
  match endianness with
  | .big => x.toByteArrayBE
  | .little => x.toByteArrayLE

def pad7 (xs : List Bit) : List Bit := Id.run $ do
  let mut ys := xs
  let w := xs.length % 7
  let m := if w == 0 then 7 else w
  for _ in [m:7] do
    ys := 0 :: ys
  pure ys

def unlead (xs : List Bit) : List Bit :=
  (xs.foldl (fun acc x =>
    if acc.1 then
      if x == Bit.zero then
        (true, acc.2)
      else
        (false, acc.2 ++ [x])
    else
      (false, acc.2 ++ [x])
  ) (true, [])).2

def ipad7 := pad7 ∘ unlead ∘ ByteArray.toBits ∘ itob

def bitNot (x : Bit) : Bit :=
  match x with
  | .one => .zero
  | .zero => .one

def onesComplement (xs : List Bit) : List Bit :=
  xs.map bitNot

def summator (x y : Bit) : (Bit × Bit) :=
  match (x, y) with
  | (.one, .one) => (.one, .zero)
  | (.zero, .one) => (.zero, .one)
  | (.one, .zero) => (.zero, .one)
  | (.zero, .zero) => (.zero, .zero)

def plusOne (xs : List Bit) : List Bit :=
  (xs.foldr (fun x acc =>
    let res := summator x acc.1
    (res.1, res.2 :: acc.2)
    -- match (x, acc.1) with
    -- (.one, .one)
  ) (Bit.one, [])).2

def twosComplement := plusOne ∘ onesComplement

def spad7 := twosComplement ∘ ipad7

def reassemble (xs : List Bit) : List Bit :=
  (xs.foldl (fun acc x =>
    let leading_bit := if acc.1 then Bit.zero else Bit.one
    let acc2' := if acc.2.1 == 6 then 0 else acc.2.1 + 1
    let acc3' := if acc.2.1 == 0 then
      acc.2.2 ++ [leading_bit, x]
    else
      acc.2.2 ++ [x]
    (false, acc2', acc3')
  ) (true, 0, [])).2.2

def uLeb128 : Nat → ByteArray :=
  Nat.toByteArrayLE ∘ Bit.bitsToNat ∘ reassemble ∘ ipad7

def sLeb128 : Nat → ByteArray :=
  Nat.toByteArrayLE ∘ Bit.bitsToNat ∘ reassemble ∘ spad7
