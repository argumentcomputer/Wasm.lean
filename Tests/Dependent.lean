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

-- Aho–Corasick string search algorithm.
-- This is a very fast way to search for a substring in a string.
-- It is used to find the first occurence of a substring in a string.
-- We use it to find the first occurence of an underscore in a string.
partial def findFirst (s : String) (sub : String) : Option String.Pos := do
  let subLen := sub.length
  let sLen := s.length
  let pospp x := String.Pos.mk $ x.byteIdx + 1
  let mut i := String.Pos.mk 0
  let mut j := 0
  let mut k := 0
  let mut lps := [0]
  while j < String.Pos.mk subLen do
    -- Debug steps
    dbg_trace s!"j: {j.byteIdx} k: {k.byteIdx} lps: {lps}"
    if sub.get! j == sub.get! k then
      k := pospp k
      -- TODO: use Array instead of this.
      lps := lps ++ [k]
      j := pospp j
    else
      if k != 0 then
        k := lps.get! k.byteIdx
      else
        lps := lps ++ [0]
        j := pospp j
  j := 0
  let mut result : Option String.Pos := .none
  while i.byteIdx < sLen do
    -- Debug steps
    dbg_trace s!"i: {i.byteIdx} j: {j.byteIdx}"
    if sub.get! j == s.get! i then
      j := pospp j
      i := pospp i
    if j == String.Pos.mk subLen then
      result := .some (i - j)
    else if i < String.Pos.mk sLen && sub.get! j != s.get! i then
      if j != 0 then
        j := lps.get! j.byteIdx
      else
        i := pospp i
  result

-- Test findFirst function on a variety of strings and substrings.
def testFindFirst : TestSeq := Id.run $ do
  -- Group tests together.
  group "findFirst:" $
    -- First test that findFirst returns .none when the substring is not found.
    test " - returns none when substring is not found" (isNone $ findFirst "hello" "world") $
    -- Now test that findFirst returns .some when the substring is found.
    test " - returns some when substring is found" (isSome $ findFirst "hello" "ll") $
    -- Now test that findFirst returns the correct position when the substring is found.
    test " - returns correct position when substring is found" $ (findFirst "hello" "ll").get! == String.Pos.mk 2


-- A function that replaces a substirng in a string.
-- We use splitAtString to split the string into two parts, then we join them back together with the replacement string.
-- def replace (s : String) (old : String) (new : String) : String :=
--   let (before, after) := splitAtString s old
--   s!"{before}{new}{after}"


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
  dbg_trace "Running tests..."
  lspecIO $
    twoPlusTwo
    -- testNat -- ++
    -- testFindFirst
