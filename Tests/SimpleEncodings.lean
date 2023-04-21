import LSpec
import Wasm.Tests

import Megaparsec.Common
import Megaparsec.Parsec
import Wasm.Wast.Parser
import Wasm.Wast.Parser.Common

open LSpec
open Wasm.Tests

open Megaparsec.Common
open Megaparsec.Parsec
open Wasm.Wast.Parser
open Wasm.Wast.Parser.Common


def testParse (parser: Parsec Char String Unit α)
              (src : String) (y : α) [BEq α] [ToString α] : TestSeq :=
  match parse parser src with
  | .error pe => test "parsing failed" (ParseFailure src pe)
  | .ok x =>
    if x == y
    then test src true
    else test "doesn't match" (ExpectationFailure s!"{y}" s!"{x}")

/-- Tests the whole whitespace: ' ', \t, \n, \r, or comments. -/
def testWhitespace : TestSeq :=
  let test' src := testParse (String.join <$> many' spaceP) src src
  test' "" ++
  test' "     " ++
  test' "   ;; arbitrary symbols" ++
  test' "   (;block comments;)  " ++
  test' "\r\n\t\t\n\r\t" ++
  test' "\r\n \t\t\n  \r\t" ++
  test' "\r\n \t(;ignore me;)\t\n  \r\t"

def testFisF : TestSeq :=
  testParse typeP "f32" (.f 32)

open Wasm.Wast.Num.Num.Int

def testMinusOneisI32MinusOne : TestSeq :=
  testParse iP "i32.const -1" ⟨ 32, -1 ⟩

open Wasm.Wast.AST
open Wasm.Wast.AST.Operation
open Wasm.Wast.AST.Type'
open Wasm.Wast.Num.Uni

instance : BEq Operation where
  beq := (toString · == toString ·)

def testAdd42IsOpAddConstStack : TestSeq :=
  testParse opsP "(i32.add (i32.const 42))"
    [.const (.i 32) (.i ⟨ 32, 42 ⟩ ), .add (.i 32)]

open Wasm.Wast.AST.Func
open Wasm.Wast.AST.Local

instance : BEq Func where
  beq := (toString · == toString ·)

def testParamIsActuallyLocal : TestSeq :=
  testParse paramP "param $t i32" (Local.mk (.some "t") (Type'.i 32))

def testSomeParamsParse : TestSeq :=
  testParse nilParamsP "(param $t i32) (param $coocoo f32) (param i64)" $
    [Local.mk (.some "t") (Type'.i 32),
      Local.mk (.some "coocoo") (Type'.f 32),
      Local.mk .none (Type'.i 64)]

def testSpacesAreIgnoredWhileParsingParams : TestSeq :=
  testParse nilParamsP "(param i32) (param $coocoo f32)  ( param i64 ) ( something_else )" $
    [Local.mk .none (Type'.i 32),
    Local.mk (.some "coocoo") (Type'.f 32),
    Local.mk .none (Type'.i 64)]

def testResultParses : TestSeq :=
  testParse brResultsP "( result i32)" [Type'.i 32]

def testBlockParses : TestSeq :=
  group "check that block instructions parse" $
  testParse opP "block (result i32) (i32.const 1)"
    (.block .none [] [.i 32] [.const (.i 32) (.i (ConstInt.mk 32 1))]) ++
  testParse opP "block (param i32) (drop)"
    (.block .none [⟨.none, .i 32⟩] [] [.drop])

def testIfParses : TestSeq :=
  group "check that if instructions parse" $
    testParse ifP "if (result i32) (then (i32.const 42)) (else (i32.const 9))"
      [.if .none [] [(Type'.i 32)]
        [(.const (Type'.i 32) (.i (ConstInt.mk 32 42)))]
        [(.const (Type'.i 32) (.i (ConstInt.mk 32 9)))]
      ]
    ++
    testParse ifP "if $x (i32.const 1) (then (br $x)) (else (br 0))"
      [ .const (.i 32) (.i ⟨32, 1⟩)
      , .if (.some "x") [] [] [.br (.by_name "x")] [.br (.by_index 0)]
      ]

def testFuncs : TestSeq :=
  let test' := testParse (bracketed funcP)
  group "check that functions parse" $
    test' "(func)" (Func.mk .none .none (.inr ([],[])) [] []) ++
    test' "(func (param $x i32) (param i32) (result i32))"
      (Func.mk .none .none
        (.inr
          ([(Local.mk (.some "x") (.i 32)), (Local.mk .none (.i 32))]
          ,[(.i 32)])
        ) [] []
      ) ++
    test' "(func (param $x i32) (param i32) (result i32) (result i64))"
      (Func.mk .none .none
        (.inr
          ([(Local.mk (.some "x") (.i 32)), (Local.mk .none (.i 32))]
          ,[(.i 32), (.i 64)])
        ) [] []
      ) ++
    test' "(func (param $x i32) (param $y i32) (result i32))"
      (Func.mk .none .none
        (.inr
          ([ (Local.mk (.some "x") (.i 32)), (Local.mk (.some "y") (.i 32))]
          ,[(.i 32)])
        ) [] []
      ) ++
    test' "(func (param $x i32) (param i32) (result i32) (i32.add (i32.const 40) (i32.const 2)))"
    (Func.mk .none .none
      (.inr
        ([(Local.mk (.some "x") (.i 32)), (Local.mk .none (.i 32))]
        ,[(.i 32)])
      )
      []
      [ .const (.i 32) (.i (ConstInt.mk 32 40))
      , .const (.i 32) (.i (ConstInt.mk 32 2))
      , .add (.i 32)
      ]
    )

def testFlawedFuncDoesntParse : TestSeq :=
  test "NO PARSE: (func func (param $x i32) (param i32) (result i32) (result i64) (result i64))" $
    not (parses? (bracketed funcP) "(func func (param $x i32) (param i32) (result i32) (result i64) (result i64))")

def testCommentsIgnored : TestSeq :=
  let test' := testParse (bracketed funcP)
  let sLine := "(func ;;(result i32)
    (nop) ;;(i32.const 23)
  )
  "
  let sBlock := "(func (;(result i32);)
    (nop) (;i32.const 23;)
  )
  "
  test "NO PARSE: (func ;; a line comment until eof)"
    (not (parses? (bracketed funcP) "(func ;; a line comment until eof)")) $
  test' sLine (Func.mk .none .none (.inr ([],[])) [] [.nop]) ++
  test' sBlock (Func.mk .none .none (.inr ([],[])) [] [.nop])

def main : IO UInt32 :=
  lspecIO $
    testWhitespace ++
    testFisF ++
    testMinusOneisI32MinusOne ++
    testAdd42IsOpAddConstStack ++
    testParamIsActuallyLocal ++
    testSomeParamsParse ++
    testSpacesAreIgnoredWhileParsingParams ++
    testResultParses ++
    testBlockParses ++
    testIfParses ++
    testFuncs ++
    testFlawedFuncDoesntParse ++
    testCommentsIgnored
