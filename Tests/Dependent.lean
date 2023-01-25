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

-- Happy path tests. We check that Nats and Floats are parsed.
def testNat : TestSeq := Id.run $ do
  -- Convert these declarations into a list of strings please.
  let nats := [
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
  -- Test that a fold of nats, parsed and checked with isSome is true.
  test "correct nats parse" $ nats.foldl (fun acc x => acc && (isSome $ mkNat' x)) true


def twoPlusTwo : TestSeq :=
  test "2 + 2 = 4" $ 2 + 2 == 4

-- Run all the TestSeq defined in this module.
def main : IO UInt32 := do
  lspecIO $
    test "four equals four" (4 = 4) ++
    twoPlusTwo ++
    testNat -- ++
    -- testFindFirst
