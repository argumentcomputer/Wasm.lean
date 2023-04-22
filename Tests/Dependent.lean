import LSpec

-- Now we import all the dependently typed stuff from Wasm project.
import Wasm.Wast.Num
import Wasm.Wast.Identifier

-- Open LSpec namespace.
open LSpec

-- Open top level namespaces.
open Wasm.Wast.Num

-- Open the namespace for the Nat, Int and Float types.
open Num.Nat
open Num.Int

-- Check if something parses to an x and not to anything else.
def parsesTo (x : Nat) (y : String) : Bool :=
  match mkNat' y with
  | some y => match y.parsed.val with
    | .ok y => y == x
    | _ => false
  | _ => false

-- No regrets about copy-pasting.
def intParsesTo (x : Int) (y : String) : Bool :=
  match mkInt' y with
  | some y => match y.parsed.val with
    | .ok y => y == x
    | _ => false
  | _ => false

-- Check if two things parse to the same Nat.
def parsesToSame (x : String) (y : String) : Bool :=
  match mkNat' x, mkNat' y with
  | some x, some y => match x.parsed.val, y.parsed.val with
    | .ok x, .ok y => x == y
    | _, _ => false
  | _, _ => false

-- No regrets about copy-pasting.
def intParsesToSame (x : String) (y : String) : Bool :=
  -- debug !
  match mkInt' x, mkInt' y with
  | some x, some y => match x.parsed.val, y.parsed.val with
    | .ok x, .ok y => x == y
    | _, _ => false
  | _, _ => false

def nats := [
  "123",
  "0",
  "0x123",
  "0x0",
  "0x1_0",
  "0x2_0_0",
  "0x3_0_0_0",
  "0x4_0_0_0_0",
  "0x5_0_0_0_0_0",
  "0x6_0_0_0_0_0_0",
  "0x7_0_0_0_0_0_0_0",
  "0x8_0_0_0_0_0_0_0_0",
  "0x9_0_0_0_0_0_0_0_0_0",
  "0x10_000_000_0_0_0"
]

-- Happy path tests. We check that Nats and Floats are parsed.
def testNat : TestSeq :=
  -- Test that a fold of nats, parsed and checked with isSome is true.
  test "correct nats parse" $ nats.foldl (fun acc x => acc && (mkNat' x).isSome) true

def testNatUnderscores : TestSeq :=
  test "correct nats parse to the same Nat with underscores" $
    nats.foldl (fun acc x => acc && parsesToSame x (x.replace "_" "")) true

def testNatAntiscores : TestSeq :=
  test "correct nats parse to different Nats than other correct nats" $
    nats.foldl (fun acc x =>
      let x' := x.replace "_" "7"
      let y := if x == x' then s!"{x}1" else x'
      acc && (not $ parsesToSame x y)
    ) true

def testBadNatsDontParse : TestSeq :=
  test "some wrong nats don't parse" $
    nats.foldl (fun acc x => acc && (mkNat' s!"..{x}").isNone) true

def testOxxDontParse : TestSeq :=
  test "more wrong nats don't parse" $
    nats.foldl (fun acc x => acc && (mkNat' s!"0xx{x}").isNone) true

def ints := [
  "123",
  "-123",
  "0",
  "-0",
  "0x123",
  "-0x123",
  "0x0",
  "-0x0",
  "0x1_0",
  "-0x1_0",
  "0x2_0_0",
  "-0x2_0_0",
  "0x3_0_0_0",
  "-0x3_0_0_0",
  "0x4_0_0_0_0",
  "-0x4_0_0_0_0",
  "0x5_0_0_0_0_0",
  "-0x5_0_0_0_0_0",
  "0x6_0_0_0_0_0_0",
  "-0x6_0_0_0_0_0_0",
  "0x7_0_0_0_0_0_0_0",
  "-0x7_0_0_0_0_0_0_0",
  "0x8_0_0_0_0_0_0_0_0",
  "-0x8_0_0_0_0_0_0_0_0",
  "0x9_0_0_0_0_0_0_0_0_0",
  "-0x9_0_0_0_0_0_0_0_0_0",
  "0x10_000_000_0_0_0",
  "-0x10_000_000_0_0_0"
]

def testInt : TestSeq :=
  test "correct ints parse" $
    ints.foldl (fun acc x => acc && (mkInt' x).isSome) true

def testIntUnderScores : TestSeq :=
  test "correct ints parse to the same Int with underscores" $
    ints.foldl (fun acc x => acc && intParsesToSame x (x.replace "_" "")) true

def testIntAntiScores : TestSeq :=
  test "correct ints parse to different Ints than other correct ints" $
    ints.foldl (fun acc x =>
      let x' := x.replace "_" "7"
      let y := if x == x' then s!"{x}1" else x'
      acc && (not $ intParsesToSame x y)
    ) true

def testBadIntsDontParse : TestSeq :=
  test "some wrong ints don't parse" $
    ints.foldl (fun acc x => acc && (mkInt' s!"..{x}").isNone) true

def testOxxIntsDontParse : TestSeq :=
  test "more wrong ints don't parse" $
    ints.foldl (fun acc x => acc && (mkInt' s!"0xx{x}").isNone) true

def floats := [
  "123.0",
  "-123.0",
  "0.0",
  "-0.0",
  "0x123.0",
  "-0x123.0",
  "0x0.0",
  "-0x0.0",
  "0x1_0.0",
  "-0x1_0.0",
  "0x2_0_0.0",
  "-0x2_0_0.0",
  "0x3_0_0_0.0",
  "-0x3_0_0_0.0",
  "0x4_0_0_0_0.0",
  "-0x4_0_0_0_0.0",
  "0x5_0_0_0_0_0.0",
  "-0x5_0_0_0_0_0.0",
  "0x6_0_0_0_0_0_0.0",
  "-0x6_0_0_0_0_0_0.0",
  "0x7_0_0_0_0_0_0_0.0",
  "-0x7_0_0_0_0_0_0_0.0",
  "0x8_0_0_0_0_0_0_0_0.0",
  "-0x8_0_0_0_0_0_0_0_0.0",
  "0x9_0_0_0_0_0_0_0_0_0.0",
  "-0x9_0_0_0_0_0_0_0_0_0.0",
  "0x10_000_000_0_0_0.0",
  "-0x10_000_000_0_0_0.0"
]

def floatsWithExponentNotation := [
  "123.0e0",
  "-123.0e0",
  "0.0e0",
  "-0.0e0",
  "0x123.0e0",
  "-0x123.0e0",
  "0x0.0e0",
  "-0x0.0e0",
  "0x1_0.0e2",
  "-0x1_0.0e0",
  "0x2_0_0.0e4",
  "-0x2_0_0.0e0",
  "0x3_0_0_0.0e-3",
  "-0x3_0_0_0.0e0",
  "0x4_0_0_0_0.0e0",
  "-0x4_0_0_0_0.0e0",
  "0x5_0_0_0_0_0.0e0",
  "-0x5_0_0_0_0_0.0e0",
  "0x6_0_0_0_0_0_0.0e0",
  "-0x6_0_0_0_0_0_0.0e0",
  "0x7_0_0_0_0_0_0_0.0e0",
  "-0x7_0_0_0_0_0_0_0.0e0",
  "0x8_0_0_0_0_0_0_0_0.0e0",
  "-0x8_0_0_0_0_0_0_0_0.0e0",
  "0x9_0_0_0_0_0_0_0_0_0.0e0",
  "-0x9_0_0_0_0_0_0_0_0_0.0e0",
  "0x10_000_000_0_0_0.0e0",
  "-0x10_000_000_0_0_0.0e0",
  "123.0e1",
  "-123.0e1",
  "0.0e1"
]


open Wasm.Wast.Identifier

def ids := [
  "lol",
  "keque",
  "foo",
  "bar",
  "baz",
  "qu$x",
  "x.y",
  "q_u.x",
  "z><x",
  "_.+-*/\\^~=<>!?@#$%&|:'`4555sdgf"
]

def testIdentifiers : TestSeq :=
  test "correct identifiers parse" $
    ids.foldl (fun acc x => acc && (mkIdentifier x).isSome) true

def testIdentifiersDontParse : TestSeq :=
  test "some wrong identifiers don't parse" $
    ids.foldl
      (fun acc x => acc && (mkIdentifier s!"{x}[]").isNone) true

def digitsWithHexDigits := [
  '0',
  '1',
  '2',
  '3',
  '4',
  '5',
  '6',
  '7',
  '8',
  '9',
  'a',
  'b',
  'c',
  'd',
  'e',
  'f',
  'A',
  'B',
  'C',
  'D',
  'E',
  'F'
]

def testDigitsWithHexDigits : TestSeq :=
  test "correct digits with hex digits parse" $
    digitsWithHexDigits.foldl
      (fun acc x => acc && (Wasm.Wast.Num.Num.Digit.mkDigit x).isSome) true

def badDigits := [
  'g',
  'h',
  'i',
  'j',
  'k',
  'l',
  'm',
  'n',
  'o',
  'p',
  'q',
  'r',
  's',
  't',
  'u',
  'v',
  'w',
  'x',
  'y',
  'z',
  'G',
  'H',
  'I',
  'J',
  'K',
  'L',
  'M',
  'N',
  'O',
  'P',
  'Q',
  'R',
  'S',
  'T',
  'U',
  'V',
  'W',
  'X',
  'Y',
  'Z'
]

def testBadDigitsDontParse : TestSeq :=
  test "some wrong digits don't parse" $
    badDigits.foldl (fun acc x =>
      acc && (Wasm.Wast.Num.Num.Digit.mkDigit x).isNone
    ) true

-- Run all the TestSeq defined in this module.
def main : IO UInt32 := do
  lspecIO $
    testNat ++
    testNatUnderscores ++
    testNatAntiscores ++
    testBadNatsDontParse ++
    testOxxDontParse ++
    (test "22_2_2 is 2222, not anything else" $ parsesTo 2222 "22_2_2") ++
    testInt ++
    testIntUnderScores ++
    testIntAntiScores ++
    testBadIntsDontParse ++
    testOxxIntsDontParse ++
    (test "-22_2_2 is -2222, not anything else" $ intParsesTo (-2222) "-22_2_2") ++
    testIdentifiers ++
    testIdentifiersDontParse ++
    testDigitsWithHexDigits ++
    testBadDigitsDontParse
