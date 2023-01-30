import LSpec

-- Now we import all the dependently typed stuff from Wasm project.
import Wasm.Wast.Num

-- Open LSpec namespace.
open LSpec

-- Open top level namespaces.
open Wasm.Wast.Num

-- Open the namespace for the Nat, Int and Float types.
open Num.Nat
open Num.Int
open Num.Float

-- Check if something is .some.
def isSome (x : Option α) : Bool :=
  match x with
  | some _ => true
  | none => false

-- Check if something is .none.
def isNone (x : Option α) : Bool :=
  match x with
  | some _ => false
  | none => true

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

-- No regrets about copy-pasting.
def floatParsesTo (x : Float) (y : String) : Bool :=
  match mkFloat' y with
  | some y => match y.parsed.val with
    | .ok y => y == x
    | _ => false
  | _ => false

-- Check if two things parse to the same Nat.
def parsesToSame (x : String) (y : String) : Bool := Id.run $ do
  match mkNat' x, mkNat' y with
  | some x, some y => match x.parsed.val, y.parsed.val with
    | .ok x, .ok y => Id.run $ do
      x == y
    | _, _ => false
  | _, _ => false

-- No regrets about copy-pasting.
def intParsesToSame (x : String) (y : String) : Bool :=
  -- debug !
  match mkInt' x, mkInt' y with
  | some x, some y => match x.parsed.val, y.parsed.val with
    | .ok x, .ok y => Id.run $ do
      x == y
    | _, _ => false
  | _, _ => false

-- No regrets about copy-pasting.
def floatParsesToSame (x : String) (y : String) : Bool :=
  match mkFloat' x, mkFloat' y with
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
def testNat : TestSeq := Id.run $ do
  -- Test that a fold of nats, parsed and checked with isSome is true.
  test "correct nats parse" $ nats.foldl (fun acc x => acc && (isSome $ mkNat' x)) true

def testNatUnderscores : TestSeq := Id.run $ do
  test "correct nats parse to the same Nat with underscores" $ nats.foldl (fun acc x => Id.run $ do
    let y := x.replace "_" ""
    acc && parsesToSame x y
  ) true

def testNatAntiscores : TestSeq := Id.run $ do
  test "correct nats parse to different Nats than other correct nats" $ nats.foldl (fun acc x => Id.run $ do
    let x' := x.replace "_" "7"
    let y := if x == x' then s!"{x}1" else x'
    acc && (not $ parsesToSame x y)
  ) true

def testBadNatsDontParse : TestSeq := Id.run $ do
  test "some wrong nats don't parse" $
    nats.foldl (fun acc x => Id.run $ do
      acc && (isNone $ mkNat' s!"..{x}")
    ) true

def testOxxDontParse : TestSeq := Id.run $ do
  test "more wrong nats don't parse" $
    nats.foldl (fun acc x => Id.run $ do
      acc && (isNone $ mkNat' s!"0xx{x}")
    ) true

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

def testInt : TestSeq := Id.run $ do
  test "correct ints parse" $ ints.foldl (fun acc x => acc && (isSome $ mkInt' x)) true

def testIntUnderScores : TestSeq := Id.run $ do
  test "correct ints parse to the same Int with underscores" $ ints.foldl (fun acc x => Id.run $ do
    let y := x.replace "_" ""
    acc && intParsesToSame x y
  ) true

def testIntAntiScores : TestSeq := Id.run $ do
  test "correct ints parse to different Ints than other correct ints" $ ints.foldl (fun acc x => Id.run $ do
    let x' := x.replace "_" "7"
    let y := if x == x' then s!"{x}1" else x'
    acc && (not $ intParsesToSame x y)
  ) true

def testBadIntsDontParse : TestSeq := Id.run $ do
  test "some wrong ints don't parse" $
    ints.foldl (fun acc x => Id.run $ do
      acc && (isNone $ mkInt' s!"..{x}")
    ) true

def testOxxIntsDontParse : TestSeq := Id.run $ do
  test "more wrong ints don't parse" $
    ints.foldl (fun acc x => Id.run $ do
      acc && (isNone $ mkInt' s!"0xx{x}")
    ) true

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

def testFloat : TestSeq := Id.run $ do
  test "correct floats parse" $ floats.foldl (fun acc x => acc && (isSome $ mkFloat' x)) true

def testFloatUnderScores : TestSeq := Id.run $ do
  test "correct floats parse to the same Float with underscores" $ floats.foldl (fun acc x => Id.run $ do
    let y := x.replace "_" ""
    acc && floatParsesToSame x y
  ) true

def testFloatAntiScores : TestSeq := Id.run $ do
  test "correct floats parse to different Floats than other correct floats" $ floats.foldl (fun acc x => Id.run $ do
    let x' := x.replace "_" "7"
    let y := if x == x' then s!"{x}1" else x'
    acc && (not $ floatParsesToSame x y)
  ) true

def testBadFloatsDontParse : TestSeq := Id.run $ do
  test "some wrong floats don't parse" $
    floats.foldl (fun acc x => Id.run $ do
      acc && (isNone $ mkFloat' s!"..{x}")
    ) true

def testOxxFloatsDontParse : TestSeq := Id.run $ do
  test "more wrong floats don't parse" $
    floats.foldl (fun acc x => Id.run $ do
      acc && (isNone $ mkFloat' s!"0xx{x}")
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
    testFloat ++
    testFloatUnderScores ++
    testFloatAntiScores ++
    testBadFloatsDontParse ++
    testOxxFloatsDontParse ++
    (test "-22_2_2.0 is -2222.0, not anything else" $ floatParsesTo (-2222.0) "-22_2_2.0")
