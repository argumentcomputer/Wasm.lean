import LSpec

import Wasm.Leb128

import YatimaStdLib.Bit

open LSpec
open Wasm.Leb128

-- https://npm.runkit.com/%40webassemblyjs%2Fleb128

instance : DecidableEq ByteArray
  | a, b => match decEq a.data b.data with
    | isTrue h₁  => isTrue $ congrArg ByteArray.mk h₁
    | isFalse h₂ => isFalse $ fun h => by cases h; exact (h₂ rfl)


def lebx : Nat := 624485
def blebx : ByteArray := ntob lebx
def bitlebx : List Bit := ByteArray.toBits blebx
def ulebx : List Bit := unlead bitlebx
def plebx : List Bit := pad7 ulebx
def nplebx : List Bit := npad7 lebx

def bigN := 1499559017

/-
5> erlang:length( "000010011000011101100101" ).
24
8> erlang:length("00001001").
8
9> erlang:length("10000111").
8
10> erlang:length("01100101").
8
11> [ 2#00001001, 2#10000111, 2#01100101 ].Is9_135_101
-/
def sanityLeb : TestSeq :=
  test "Sanity check: uLeb128 1 is #[1]" $ uLeb128 1 = ByteArray.mk #[1]

def testLebx : TestSeq :=
  group "Big endian 624485" $
    test "to bytes" (blebx = ByteArray.mk #[9,135,101]) $
    test "converted to bits"
      (bitlebx = [0,0,0,0,1,0,0,1,1,0,0,0,0,1,1,1,0,1,1,0,0,1,0,1]) $
    test "without leading zeroes"
      (ulebx =           [1,0,0,1,1,0,0,0,0,1,1,1,0,1,1,0,0,1,0,1]) $
    test "7-bit padded"
      (plebx =         [0,1,0,0,1,1,0,0,0,0,1,1,1,0,1,1,0,0,1,0,1])

def testCanPad7Naturals : TestSeq :=
  -- 01001 10000 11101 10010 1 with spaces between each bit:
  --                          0 1 0 0 1|1 0 0 0 0|1 1 1 0 1|1 0 0 1 0|1
  let expected : List Bit := [0,1,0,0,1,1,0,0,0,0,1,1,1,0,1,1,0,0,1,0,1]
  let actual := npad7 lebx
  test "Nat 7-bit padded" $ actual = expected ∧ actual = plebx

def testBigN : TestSeq :=
  group "Big number" $
    test "big endian" (uLeb128 bigN = ByteArray.mk #[233, 232, 133, 203, 5]) $
    test "7-bit padded, reassembled" $
      -- 0000010111001011100001011110100011101001
      let expected : List Bit :=
        [0,0,0,0, 0,1,0,1, 1,1,0,0, 1,0,1,1, 1,0,0,0, 0,1,0,1, 1,1,1,0,
         1,0,0,0, 1,1,1,0, 1,0,0,1]
      reassemble (npad7 bigN) = expected

def testUnsignedLeb128 : TestSeq :=
  group "Unsigned LEB128" $
    test "of 624485" (uLeb128 lebx = ByteArray.mk #[229, 142, 38]) $
    test "of 9000" (uLeb128 9000 = ByteArray.mk #[168, 70])

def testSignedLeb128 : TestSeq :=
  group "Signed LEB128" $
    test "of -1" (sLeb128 (-1) = ByteArray.mk #[127]) $
    test "of 9000" (sLeb128 9000 = ByteArray.mk #[168, 198, 0]) $
    test "of 8787" (sLeb128 8787 = ByteArray.mk #[211, 196, 0]) $
    test "of -123456" (sLeb128 (-123456) = ByteArray.mk #[192, 187, 120]) $
    test "of 624485" (sLeb128 624485 = ByteArray.mk #[229, 142, 38])


def main : IO UInt32 := do
  lspecIO $
    testLebx ++
    testCanPad7Naturals ++
    testBigN ++
    testUnsignedLeb128 ++
    testSignedLeb128
