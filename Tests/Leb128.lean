import LSpec

import Wasm.Leb128

import YatimaStdLib.Bit

open LSpec
open Wasm.Leb128

  -- let bigN := 1499559017
  -- IO.println s!"{uLeb128 bigN} should be 233 232 133 203 5"
  -- IO.println s!"{reassemble $ npad7 bigN} should be 00000101 11001011 10000101 11101000 11101001"
  -- IO.println s!"= = = = SIGNED LEB128 TEST = = = ="
  -- IO.println s!"{sLeb128 (-123456)} should be [192, 187, 120]"
  -- IO.println s!"{sLeb128 (1)} should be [1]"
  -- IO.println s!"{sLeb128 (624485)} should be 229, 142, 38"

def lebx : Nat := 624485
def blebx : ByteArray := ntob lebx
def bitlebx : List Bit := ByteArray.toBits blebx
def ulebx : List Bit := unlead bitlebx
def plebx : List Bit := pad7 ulebx
def nplebx : List Bit := npad7 lebx

/-
5> erlang:length( "000010011000011101100101" ).
24
8> erlang:length("00001001").
8
9> erlang:length("10000111").
8
10> erlang:length("01100101").
8
11> [ 2#00001001, 2#10000111, 2#01100101 ].
-/
def testBlebxIs9_135_101 : TestSeq := Id.run $ do
  let expected : ByteArray := ByteArray.mk #[9,135,101]
  let actual := ntob lebx
  test "Big endian 624485 should be ByteArray.mk #[9,135,101]" $
    expected.data == actual.data &&
    actual.data == blebx.data

def testBitlebxIs000010011000011101100101 : TestSeq := Id.run $ do
  -- 00001 00110 00011 10110 0101 with spaces between each bit:
  --                          0 0 0 0 1|0 0 1 1 0|0 0 0 1 1|1 0 1 1 0|0 1 0 1
  let expected : List Bit := [0,0,0,0,1,0,0,1,1,0,0,0,0,1,1,1,0,1,1,0,0,1,0,1]
  let actual := ByteArray.toBits blebx
  --                      0 0 0 0 1|0 0 1 1 0|0 0 0 1 1|1 0 1 1 0|0 1 0 1
  test "Big endian 624485 converted to bits should be [0,0,0,0,1,0,0,1,1,0,0,0,0,1,1,1,0,1,1,0,0,1,0,1]" $
    expected == actual &&
    actual == bitlebx

def testUlebxIs10011000011101100101 : TestSeq := Id.run $ do
  -- 10011 00001 11011 00101 with spaces between each bit:
  --                          1 0 0 1 1|0 0 0 0 1|1 1 0 1 1|0 0 1 0 1
  -- ===                      1|0 0 1 1 0|0 0 0 1 1|1 0 1 1 0|0 1 0 1
  let expected : List Bit := [1,0,0,1,1,0,0,0,0,1,1,1,0,1,1,0,0,1,0,1]
  let actual := unlead bitlebx
  test "Big endian 624485 in binary without leading zeroes should be [1,0,0,1,1,0,0,0,0,1,1,1,0,1,1,0,0,1,0,1]" $
    expected == actual &&
    actual == ulebx

def testPad7UlebxIs010011000011101100101 : TestSeq := Id.run $ do
  -- 01001 10000 11101 10010 1 with spaces between each bit:
  --                          0 1 0 0 1|1 0 0 0 0|1 1 1 0 1|1 0 0 1 0|1
  let expected : List Bit := [0,1,0,0,1,1,0,0,0,0,1,1,1,0,1,1,0,0,1,0,1]
  let actual := pad7 ulebx
  test "Big endian 624485 in binary without leading zeroes 7-bit padded should be [0,1,0,0,1,1,0,0,0,0,1,1,1,0,1,1,0,0,1,0,1]" $
    expected == actual

def testCanPad7Naturals : TestSeq := Id.run $ do
  -- 01001 10000 11101 10010 1 with spaces between each bit:
  --                          0 1 0 0 1|1 0 0 0 0|1 1 1 0 1|1 0 0 1 0|1
  let expected : List Bit := [0,1,0,0,1,1,0,0,0,0,1,1,1,0,1,1,0,0,1,0,1]
  let actual := npad7 lebx
  test "Number 624485, 7-bit padded should be [0,1,0,0,1,1,0,0,0,0,1,1,1,0,1,1,0,0,1,0,1]" $
    expected == actual &&
    actual == nplebx &&
    actual == plebx

def testUnsignedLeb128 : TestSeq := Id.run $ do
  let expected : ByteArray := ByteArray.mk #[229, 142, 38]
  let actual := uLeb128 lebx
  test "Unsigned LEB128 of 624485 should be ByteArray.mk #[ 229, 142, 38 ] and 1 is ByteArray.mk #[1]" $
    expected.data == actual.data &&
    (uLeb128 1).data == (ByteArray.mk #[1]).data

def bigN := 1499559017

def testBigNIs233_232_133_203_5 : TestSeq := Id.run $ do
  let expected : ByteArray := ByteArray.mk #[233, 232, 133, 203, 5]
  let actual := uLeb128 bigN
  test "Big endian 1499559017 should be ByteArray.mk #[233, 232, 133, 203, 5]" $
    expected.data == actual.data

-- 0000010111001011100001011110100011101001
def testBigNReassembledAfterNPad7Is0000010111001011100001011110100011101001 : TestSeq := Id.run $ do
  -- 0000010111001011100001011110100011101001 with spaces between each bit:
  --                          0 0 0 0  0 1 0 1  1 1 0 0  1 0 1 1  1 0 0 0  0 1 0 1  1 1 1 0  1 0 0 0  1 1 1 0  1 0 0 1
  let expected : List Bit := [0,0,0,0, 0,1,0,1, 1,1,0,0, 1,0,1,1, 1,0,0,0, 0,1,0,1, 1,1,1,0, 1,0,0,0, 1,1,1,0, 1,0,0,1]
  --                         [0,0,0,0, 0,1,0,1, 1,1,0,0, 1,0,1,1, 1,0,0,0, 0,1,0,1, 1,1,1,0, 1,0,0,0, 1,1,1,0, 1,0,0,1]
  let actual := reassemble $ npad7 bigN
  test "Big endian 1499559017, 7-bit padded, reassembled should be [0,0,0,0,0,1,0,1,1,1,0,0,1,0,1,1,1,0,0,0,0,1,0,1,1,1,1,0,1,0,0,0,1,1,0,1,0,0,0,1]" $
    expected == actual

def signed_lebxs := [ (-123456, ByteArray.mk #[192, 187, 120]), (624485, ByteArray.mk #[229, 142, 38]) ]

def testSignedLeb128 : TestSeq := Id.run $ do
  let expected : List (Int × ByteArray) := signed_lebxs
  let actual := List.map (λ (n : Int × ByteArray) => (n.1, sLeb128 n.1)) signed_lebxs
  test "Signed LEB128 of -123456 should be ByteArray.mk #[192, 187, 120] and 624485 is ByteArray.mk #[229, 142, 38]" $
    -- Pairwise compair each element's first element and second element between expected and actual.
    -- Implementation follows:
    actual.all $
      fun (n : Int × ByteArray) =>
        expected.any (fun (m : Int × ByteArray) => n.1 == m.1 && n.2.data == m.2.data)

def testSignedLeb128HitherThither : TestSeq := Id.run $ do
  -- IO.println s!"{uLeb128 9000} should be 168, 70 (checked with https://npm.runkit.com/%40webassemblyjs%2Fleb128)"
  test "Signed LEB128 of -1 is [127], signed leb of 9000 is [168, 198, 0], whereas unsigned leb is [168, 70]. And signed leb of 8787 is [211, 196, 0]" $
    (sLeb128 (-1)).data == (ByteArray.mk #[127]).data &&
    (sLeb128 9000).data == (ByteArray.mk #[168, 198, 0]).data &&
    (sLeb128 8787).data == (ByteArray.mk #[211, 196, 0]).data &&
    -- U is different!
    (uLeb128 9000).data == (ByteArray.mk #[168, 70]).data


def main : IO UInt32 := do
  lspecIO $
    testBlebxIs9_135_101 ++
    testBitlebxIs000010011000011101100101 ++
    testUlebxIs10011000011101100101 ++
    testPad7UlebxIs010011000011101100101 ++
    testCanPad7Naturals ++
    testUnsignedLeb128 ++
    testBigNReassembledAfterNPad7Is0000010111001011100001011110100011101001 ++
    testSignedLeb128 ++
    testSignedLeb128HitherThither
