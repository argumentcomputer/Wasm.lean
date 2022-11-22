import YatimaStdLib

namespace Wasm.Leb128

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

def nattob (x : Nat) (endianness : Endian := .big) : ByteArray :=
  match endianness with
  | .big => x.toByteArrayBE
  | .little => x.toByteArrayLE

def modPad (modulo : Nat) (bs : List Bit)
           (padWith : Bit := .zero) (endianness : Endian := .big)
           : List Bit := Id.run $ do
  let l := bs.length
  let rem := l % modulo
  let to_replicate := if rem == 0 then
    0
  else
    modulo - rem
  let pad := List.replicate to_replicate padWith
  match endianness with
  | .big => pad ++ bs
  | .little => bs ++ pad

def ntob (n : Nat) (endianness : Endian := .big) : ByteArray :=
  match endianness with
  | .big => n.toByteArrayBE
  | .little => n.toByteArrayLE

def pad7 (xs : List Bit) : List Bit := Id.run $ do
  modPad 7 xs

/- Remove all the leading zeroes -/
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

def npad7 := pad7 ∘ unlead ∘ ByteArray.toBits ∘ ntob

def spad7 (x : Int) : List Bit :=
  let go := npad7 ∘ Int.natAbs
  (if x >= 0 then
    go
  else
    twosComplement ∘ go) x

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

def LebCore : List Bit → ByteArray :=
  Nat.toByteArrayLE ∘ Bit.bitsToNat ∘ reassemble

def uLeb128 : Nat → ByteArray :=
  LebCore ∘ npad7

def sLeb128 : Int → ByteArray :=
  LebCore ∘ spad7
