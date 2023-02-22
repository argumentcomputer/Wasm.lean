import LSpec

import Megaparsec.Parsec
import Wasm.Wast.Parser

open LSpec

open Megaparsec.Parsec
open Wasm.Wast.Parser

def isOkAndBEq (x : Except ε α) (y : α) [BEq α] : Bool :=
  match x with
  | .ok actual => y == actual
  | .error _ => false

def testParse (parser: Parsec Char String Unit α)
              (x : String) (y : α) [BEq α] : Bool :=
  isOkAndBEq (parse parser x) y

open Wasm.Wast.AST.Type'.Type'

def testFisF : TestSeq :=
  test "f32 parses to .f 32" $ testParse typeP "f32" (f 32)

open Wasm.Wast.Num.Num.Int

def testMinusOneisI32MinusOne : TestSeq :=
  test "parse 'i32 const -1'" $
    testParse iP "i32.const -1" ⟨ 32, -1 ⟩

open Wasm.Wast.AST.Operation
open Wasm.Wast.AST.Type'
open Wasm.Wast.Num.Uni

/-

Recap:

  inductive Operation where
  | nop
  | const : Type' → NumUniT → Operation
  | add : Type' → Get' → Get' → Operation
  | block : List Type' → List Operation → Operation
  | loop : List Type' → List Operation → Operation
  | if : List Type' → List Operation → List Operation → Operation
  | br : LabelIndex → Operation
  | br_if : LabelIndex → Operation

-/

instance : BEq Operation where
  beq := (toString · == toString ·)

def testAdd42IsOpAddConstStack : TestSeq :=
  test "'i32.add (i32.const 42)' parses to '.add (.i 32) (Get'.from_operation (ConstInt 32 42)) (Get'.from_stack)'" $
    testParse (binopP "add" .add) "i32.add (i32.const 42)" $
      Operation.add (.i 32)
                    (.from_operation (.const (.i 32) (.i ⟨ 32, 42 ⟩ )))
                    (.from_stack)

def testAdd42IsntOpAddWrongConstStack : TestSeq :=
  test "'i32.add (i32.const 42)' DOES NOT parse to '.add (.i 32) (Get'.from_operation (ConstInt 32 420)) (Get'.from_stack)'" $
    let unexpect :=
      Operation.add (.i 32)
                    (.from_operation (.const (.i 32) (.i ⟨ 32, 420 ⟩ )))
                    (.from_stack)
    not (testParse (binopP "add" .add) "i32.add (i32.const 42)" $ unexpect)

open Wasm.Wast.AST.Func

instance : BEq Func where
  beq := (toString · == toString ·)

def testFuncIsFunc : TestSeq :=
  test "(func) is (Func.mk none none [] [] [] [])" $ testParse funcP "(func)" (Func.mk .none .none [] [] [] [])

open Wasm.Wast.AST.Local

def testParamIsActuallyLocal : TestSeq :=
  test "param $t i32 is (Local.mk 0 .none (Type'.i 32))" $ testParse paramP "param $t i32" (Local.mk (.some "t") (Type'.i 32))

def testSomeParamsParse : TestSeq :=
  test "(param $t i32) (param $coocoo f32) (param i64) parses correctly." $
    testParse nilParamsP "(param $t i32) (param $coocoo f32) (param i64)" $
      [Local.mk (.some "t") (Type'.i 32),
       Local.mk (.some "coocoo") (Type'.f 32),
       Local.mk .none (Type'.i 64)]

def testSpacesAreIgnoredWhileParsingParams : TestSeq :=
  test "(param i32) (param $coocoo f32)  ( param i64 ) ( something_else ) parses alright" $
    testParse nilParamsP "(param i32) (param $coocoo f32)  ( param i64 ) ( something_else )" $
      [Local.mk .none (Type'.i 32),
       Local.mk (.some "coocoo") (Type'.f 32),
       Local.mk .none (Type'.i 64)]

def testResultParses : TestSeq :=
  test "( result i32) parses to [Type'.i 32]" $
    testParse brResultsP "( result i32)" [Type'.i 32]

def testFuncParses : TestSeq :=
  test "(func (param $x i32) (param $y i32) (result i32)
  ) parses" $
    testParse funcP "(func (param $x i32) (param $y i32) (result i32)
  )" $ (Func.mk .none .none [(Local.mk (.some "x") (Type'.i 32)), (Local.mk (.some "y") (Type'.i 32))] [(Type'.i 32)] [] [])

def testAnotherFuncParses : TestSeq :=
  test "(func (param $x i32) (param i32) (result i32)) parses" $
    testParse funcP "(func (param $x i32) (param i32) (result i32))" $ (Func.mk .none .none [(Local.mk (.some "x") (Type'.i 32)), (Local.mk .none (Type'.i 32))] [(Type'.i 32)] [] [])

def testYetAnotherFuncParses : TestSeq :=
  test "(func (param $x i32) (param i32) (result i32) (result i64)) parses" $
    testParse funcP "(func (param $x i32) (param i32) (result i32) (result i64))" $ (Func.mk .none .none [(Local.mk (.some "x") (Type'.i 32)), (Local.mk .none (Type'.i 32))] [(Type'.i 32), (Type'.i 64)] [] [])

def testFlawedFuncDoesntParse : TestSeq :=
  test "(func func (param $x i32) (param i32) (result i32) (result i64) (result i64)) DOES NOT parse" $
    not (parses? funcP "(func func (param $x i32) (param i32) (result i32) (result i64) (result i64))")

def testBlockResultConstEndParses : TestSeq :=
  test "(block (result i32) (i32.const 1) end) parses" $
    testParse opP "(block (result i32) (i32.const 1) end)" $
      (.block [(Type'.i 32)] [(.const (Type'.i 32) (.i (ConstInt.mk 32 1)))])

def testIfParses : TestSeq :=
  test "if (result i32) then (i32.const 42) else (i32.const 9) parses" $
    testParse ifP "if (result i32) then (i32.const 42) else (i32.const 9)" $
      (.if [(Type'.i 32)] [(.const (Type'.i 32) (.i (ConstInt.mk 32 42)))]
           [(.const (Type'.i 32) (.i (ConstInt.mk 32 9)))])

def testAFuncWithImplementationParses : TestSeq :=
  test "(func (param $x i32) (param i32) (result i32) (i32.add (i32.const 40) (i32.const 2))) parses" $
    testParse funcP "(func (param $x i32) (param i32) (result i32) (i32.add (i32.const 40) (i32.const 2)))" $
      (Func.mk .none .none
        [(Local.mk (.some "x") (Type'.i 32)), (Local.mk .none (.i 32))]
        [(.i 32)] []
        [(.add (.i 32) (.from_operation (.const (.i 32) (.i (ConstInt.mk 32 40))))
          (.from_operation (.const (.i 32) (.i (ConstInt.mk 32 2))))
         )])

def main : IO UInt32 := do
  lspecIO $
    testFisF ++
    testMinusOneisI32MinusOne ++
    testAdd42IsOpAddConstStack ++
    testAdd42IsntOpAddWrongConstStack ++
    testFuncIsFunc ++
    testParamIsActuallyLocal ++
    testSomeParamsParse ++
    testSpacesAreIgnoredWhileParsingParams ++
    testResultParses ++
    testFuncParses ++
    testAnotherFuncParses ++
    testYetAnotherFuncParses ++
    testFlawedFuncDoesntParse ++
    testBlockResultConstEndParses ++
    testIfParses ++
    testAFuncWithImplementationParses