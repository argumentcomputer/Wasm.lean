import YatimaStdLib.Bit
import YatimaStdLib.Int

namespace Wasm.Leb128

def modPad (modulo : Nat) (bs : List Bit)
           (padWith : Bit := .zero) (endianness : Endian := .big)
           : List Bit :=
  let rem := bs.length % modulo
  let to_replicate := if rem = 0 then 0 else modulo - rem
  let pad := List.replicate to_replicate padWith
  match endianness with
  | .big => pad ++ bs
  | .little => bs ++ pad

def ntob (n : Nat) (endianness : Endian := .big) : ByteArray :=
  match endianness with
  | .big => n.toByteArrayBE
  | .little => n.toByteArrayLE

def nmodPad (pad : Nat) (n : Nat) (endianness : Endian := .big) : List Bit :=
  modPad pad ∘ Bit.unlead ∘ ByteArray.toBits $ ntob n endianness

/-- This is a textbook LEB128 implementation based on `Int` bitwise arithmetics:
https://en.wikipedia.org/wiki/LEB128

The simplistic overview of the (unsigned) algorithm:
1. split binary representation into groups of 7 bits
2. add high bits to all but last (most significant) group to form bytes

**Example from Wikipedia:**
```
N = 624485
MSB ------------------ LSB
      10011000011101100101  In raw binary
     010011000011101100101  Padded to a multiple of 7 bits
 0100110  0001110  1100101  Split into 7-bit groups
00100110 10001110 11100101  Add high 1 bits on all but last (most significant)
                            group to form bytes
    0x26     0x8E     0xE5  In hexadecimal

→ 0xE5 0x8E 0x26            Output stream (LSB to MSB)
```

The signed algorithm is largely the same.

The following function implements the following pseudocode from Wikipedia:

```
while (more bytes) {
  byte = low-order 7 bits of value;
  value >>= 7; // shifts the value to the next "group of 7 bits"

  if    (value ==  0 && sign bit of byte is clear)
     || (value == -1 && sign bit of byte is set)
    more bytes = false;
  else
    set high-order bit of byte;
  add byte to result;
}
```

We'll use three bitmaps:
- 0x40 : 01000000. bitwise AND extracts the second-highest bit (sign bit)
- 0x80 : 10000000. bitwise AND extracts the highest bit
- 0x7f : 01111111. bitwise AND extracts the 7 lowest bits

-/
private partial def lebCore (unsigned? : Bool)
                    (acc : ByteArray) (val byte : Int) : ByteArray :=
  let lastByte? := if unsigned?
    then val = 0 -- if unsigned leb, we only need to check if it's the last byte
    else -- if signed...
    -- if pos last byte AND sign bit is unset
      (val =  0          &&  (byte &&& 0x40) = 0) ||
      -- OR
    -- if neg last byte AND sign bit is set
      (val = -1          &&  (byte &&& 0x40) ≠ 0)
  if lastByte?
    then acc.push $ byte.toUInt8 -- if the sign bit is correct, we're done
    else
      let byte' := byte ||| 0x80 -- else, set the high bit to continue
      lebCore unsigned? (acc.push $ byte'.toUInt8) (val >>> 7) (val &&& 0x7f)

/-- Encode the given `Int` to a `ByteArray` using _unsigned_ Leb128. -/
def uLeb128 (x : Nat) : ByteArray :=
  lebCore true default (x >>> 7) (x &&& 0x7f)

/-- Encode the given `Int` to a `ByteArray` using _signed_ Leb128. -/
def sLeb128 (x : Int) : ByteArray :=
  lebCore false default (x >>> 7) (x &&& 0x7f)
