import LSpec
import Megaparsec.Parsec

import Wasm.Leb128
import Wasm.Wast.Num

import YatimaStdLib.Bit
import YatimaStdLib.String

open LSpec
open Megaparsec.Parsec
open Wasm.Leb128
open Wasm.Wast.Num.Num.Int

/- This uses the testsuite files from @mohanson's python leb128 implementation:
https://github.com/mohanson/leb128/tree/master/test
 -/

-- https://npm.runkit.com/%40webassemblyjs%2Fleb128

open Megaparsec.Errors.Bundle in
inductive ParseFailure (src : String) (e : ParseErrorBundle Char String Unit) : Prop
instance : Testable (ParseFailure src e) := .isFailure s!"Parsing:\n{src}\n{e}"

def lebx : Nat := 624485
def blebx : ByteArray := ntob lebx
def bitlebx : List Bit := blebx.toBits
def ulebx : List Bit := Bit.unlead bitlebx
def plebx : List Bit := modPad 7 ulebx
def nplebx : List Bit := nmodPad 7 lebx

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
  let actual := nmodPad 7 lebx
  test "Nat 7-bit padded" $ actual = expected ∧ actual = plebx

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


open Wasm.Wast.Num (bytesFromHexP) in
def testPair (unsigned? : Bool) (acc : TestSeq) (line : String) : TestSeq :=
  if let [nstr, expectedstr] := line.splitOn
    then match parseInt' "" nstr, parse bytesFromHexP expectedstr with
    | .ok n, .ok expected => if unsigned?
      then test s!"of {n}ᵤ" (uLeb128 n.natAbs = expected) acc
      else test s!"of {n}ₛ" (sLeb128 n = expected) acc
    | .error e, _ => test "number parsing" (ParseFailure nstr e)
    | .ok _, .error e => test "bytes parsing" (ParseFailure expectedstr e)
    else test "wrong line format" false

open IO.FS in
def main : IO UInt32 := do
  let unsigneds ← lines "./Tests/Data/leb128/unsigned.txt"
  let signeds ← lines "./Tests/Data/leb128/signed.txt"
  lspecIO $
    testLebx ++
    testCanPad7Naturals ++
    testUnsignedLeb128 ++
    testSignedLeb128 ++
    group "Unsigned LEB128" (unsigneds.toList.foldl (testPair true) .done) ++
    group "Signed LEB128" (signeds.toList.foldl (testPair false) .done)
