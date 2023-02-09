import YatimaStdLib.Bit

namespace Wasm.Leb128

def nattob (x : Nat) (endianness : Endian := .big) : ByteArray :=
  match endianness with
  | .big => x.toByteArrayBE
  | .little => x.toByteArrayLE

def modPad (modulo : Nat) (bs : List Bit)
           (padWith : Bit := .zero) (endianness : Endian := .big)
           : List Bit := Id.run $ do
  let rem := bs.length % modulo
  let to_replicate := if rem == 0 then 0 else modulo - rem
  let pad := List.replicate to_replicate padWith
  match endianness with
  | .big => pad ++ bs
  | .little => bs ++ pad

def ntob (n : Nat) (endianness : Endian := .big) : ByteArray :=
  match endianness with
  | .big => n.toByteArrayBE
  | .little => n.toByteArrayLE

def pad7 (xs : List Bit) : List Bit := modPad 7 xs

/- Remove all the leading zeroes -/
def unlead (xs : List Bit) : List Bit := xs.dropWhile (· = .zero)

def npad7 := pad7 ∘ unlead ∘ ByteArray.toBits ∘ ntob

def sDisambiguatePosInt (xs : List Bit) : ByteArray :=
  let go := Nat.toByteArrayLE ∘ Bit.bitsToNat
  match xs with
  | .zero :: .one :: rest => go (.one :: .one :: rest) ++ ByteArray.mk #[0]
  | _ => go xs

def spad7 (x : Int) : List Bit :=
  let padded := npad7 x.natAbs
  if x >= 0 then padded else Bit.twosComplement padded

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

def sLeb128 (x : Int) : ByteArray :=
  if x ≥ 0 then
    sDisambiguatePosInt ∘ reassemble $ spad7 x
  else
    LebCore $ spad7 x
