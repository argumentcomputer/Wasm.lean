import LSpec
import Megaparsec.Parsec
import Wasm.Wast.Parser
import Wasm.Bytes

import Wasm.Tests

open LSpec
open Megaparsec.Parsec
open Wasm.Wast.Parser
open Wasm.Bytes

open Wasm.Tests

/- Generic Wasm module test. -/
partial def testGeneric : String → ByteArray → ByteArray → TestSeq
  | mod, rs, os =>
    let str := s!"Binary representation is compatible with {dumpFname mod}
    {mod}"

/- Here's how Main used to test a particular module:

  IO.println s!"{i} is represented as:"
  let o_parsed_module ← parseTestP moduleP i
  match o_parsed_module.2 with
  | .error _ => IO.println "FAIL"
  | .ok parsed_module => do
    IO.println s!">>> !!! >>> It is converted to bytes as: {mtob parsed_module}"
    let f := System.mkFilePath ["/tmp", "mtob.41.wasm"]
    let h ← IO.FS.Handle.mk f IO.FS.Mode.write
    h.write $ mtob parsed_module
    gO.println "It's recorded to disk at /tmp/mtob.41.wasm"

Instead of this, here, we're going to:

 1. Make the reference WASM bytes with `wasm-sandbox` invocation,
    as provided by function `w2b`.
 2. Read the reference bytes into a variable.
 3. Compile our bytes and read those into a variable.
 4. Write our bytes into a file called s!"{dumpFname}.lean".
 5. Byte by byte, compare the two variables, reporting errors.
-/
open IO.FS in
partial def moduleTestSeq (x : String) : IO TestSeq := do
  -- Run w2b against x
  match ←w2b x with
  | .ok _ => do
    -- Read the reference bytes into a variable.
    let ref_bytes ← readBinFile $ dumpFname x
    -- Compile our bytes and read those into a variable.
    match parse moduleP x with
    | .error pe =>
      pure $ test "parsing module" (ParseFailure x pe)
    | .ok module => do
      let our_bytes := mtob module
      -- Write our bytes into a file called s!"{dumpFname}.lean".
      writeBinFile s!"{dumpFname x}.lean" our_bytes
      pure $ testGeneric x ref_bytes our_bytes
  | .error e =>
    pure $ test s!"failed to encode with wasm-sandbox: {x}" (ExternalFailure e)

def uWasmMods := [
  "(module
        (func (export \"main\")
            (result i32)

            (i32.add
                (i32.const 1499550000)
                (i32.add (i32.const 9000) (i32.const 17))
            )
        )
    )",
    "(module
        (func (export \"two_ints\")
            (result i32) (result i32)
            (i32.add
                (i32.const 1499550000)
                (i32.add (i32.const 9000) (i32.const 17))
            )
            (i32.add (i32.const -1) (i32.const 1))
        )
    )",
    "(module
        (func (param $x_one i32) (param $three i32) (param $y_one i32)
          (result i32) (i32.add (i32.const 40) (i32.const 2)))
        (func (param $x_two f32) (param f32) (param f32) (result i32)
          (i32.add (i32.const 12) (i32.const 30)))
    )",
    "(module
      (func (param $x i32) (param i32) (result i32)
      (i32.add (i32.const 40) (i32.const 2)))
    )",
    "(module
        ( func (param $x i32) (param i32) )
      )",
    "(module
        (func (param $x i32))
      )",
    "(module
        ( func )
      )",
    "(module
        ( func ) (func $x)
      )",
    "(module)",
    "(module
      (func $main (export \"main\")
        (param $x i32)
        (param i32)
        (result i32 i32)

        (block (result i32) (i32.const 3) (i32.add (br 0) (i32.const 9)))
        (i32.add
          (i32.const 1499550000)
          (i32.add (i32.const 9000) (i32.const 17))
        )

      )
    )",
    "(module
      (func $main (export \"main\")
        (param $x i32)
        (param $y i32)
        (result i32 i32)

        (i32.add
          (i32.const 1499550000)
          (i32.add (i32.const 17) (i32.const 9000))
        )

      )
    )"
]

def modsControl :=
  [ "(module (func) (func (nop)))"
  , "(module (func (result i32) (i32.const 0)) (func (result i32) (i32.const 1)))" -- Here we check if non-0-output function return types are also mashed together.
  , "(module (func (result i32)
        (block (result i32) (i32.const 3))
     ))"
  , "(module (func (result i32)
        (if (result i32) (i32.const 0)
          (then (i32.const 1)) (else (i32.const 0))
        )
     ))"
  , "(module (func (result i32)
        (loop (result i32) (i32.const 3))
     ))"
  , "(module (func (result i64)
        (block (result i64)
          (i64.const 6)
          (i64.add (br 0))
        )
     ))"
  , "(module (func (result i32)
        (block (result i32) (i32.ctz (br_if 0)))
     ))"
  , "(module (func (result i32)
        (block $name (result i32) (i32.ctz (br_if 0)))
     ))"
  , "(module (func
        (block $two (loop (block $zero (br_if $two))))
     ))"
  , "(module (func
        (block $two (loop (block $zero (br_if $two))))
        (block $xxx (nop))
     ))"
  , "(module (func
        (block $two (loop (block $zero (br_if $two))))
       )
       (func $f
        (block $one (nop))
       )
     )"
  , "(module (func
        (block $shadow (loop (block $shadow (br_if $shadow))))
     ))"
  , "(module (func (result i32)
        (loop $aaaaaaaaaaaaaaaaaaaaa (result i32) (i32.const 3))
     ))"
  , "(module (func (result i32)
        (if $x (result i32) (i32.const 1) (then (i32.const 4) (br $x))
          (else (i32.const 256) (br 0)))
     ))"
  , "(module
        (func (export \"break-multi-value\") (result i32 i32 i64)
          (block (result i32 i32 i64)
            (i32.const 0) (i32.const 0) (i64.const 0)
            (loop (param i32 i32 i64)
              (block (i32.const 18) (i32.const -18) (i64.const 18) (br 2))
              (i32.const 20) (i32.const -20) (i64.const 20) (br 0)
            )
            (i32.const 19) (i32.const -19) (i64.const 19)
          )
        )
        (func (param i64) (result i32) (local.get 0) (drop) (i32.const 4))
     )"
  , "(module
       (func (result i32)
          (i32.const 1)
          (block (param i32) (result i32)
            (i32.const 2)
            (i32.add)
          )
        )
     )"
  , "(module
       (func (result i64 i32)
          (block (result i64 i32)
            (i64.const 33)
            (i32.const 1)
            (i32.const 2)
            (i32.add)
          )
        )
     )"
  ]

def modsLocal :=
  [
    "(module (func (export \"type-local-i32\") (result i32)
        (local i32) (local.get 0)
      ))"
  , "(module (func (export \"type-param-i64\") (param i64) (result i64)
         (local.get 0)
      ))"
  , "(module (func (param i32) (result i32)
        (loop (result i32) (local.get 0))
      ))"
  , "(module (func (param i32) (result i32)
        (block (result i32) (local.get 0) (i32.const 1) (br_if 0))
      ))"
  , "(module (func (result i32) (local $a i32)
        (block (result i32) (local.get $a) (local.get 0) (br_if 0))
      ))"
  , "(module (func (export \"as-block-value\") (param i32)
        (block (i32.const 1) (local.set 0))
  ))"
  , "(module (func (param i32)
        (loop (i32.const 3) (local.set 0))
  ))"
  , "(module (func (param i32)
        (if (local.get 0) (then) (else (local.set 0) (i32.const 1)))
  ))"
  , "(module (func (param i32) (result i32)
        (i32.ne (i32.const 10) (local.tee 0))
  ))"
  , "(module (func (export \"type-mixed\") (param i64 f32 f64 i32 i32) (local f32 i64 i64 f64)
    (drop) (i64.const 0) (i64.eqz (local.tee 0))
    (drop) (i32.const 0) (i32.eqz (local.tee 3))
    (drop) (i32.const 0) (i32.eqz (local.tee 4))
    (drop) (i64.const 0) (i64.eqz (local.tee 6))
    (drop) (i64.const 0) (i64.eqz (local.tee 7))
  ))"
  ]

def modsGlobal :=
  [
    "(module
       (global $a i32 (i32.const -2)) (global i32 (i32.const -3))
       (global $b i64 (i64.const -5))
       (func (result i64) (global.get $b))
       (func (export \"as-if-else\") (result i32)
         (if (result i32) (i32.const 0)
           (then (i32.const 2)) (else (global.get 1))
         )
       )
     )"
  , "(module (global $a i32 (i32.const -2)))"
  , "(module
       (global i32 (i32.const 17)) (global $a i32 (i32.const -2))
       (func (param i32) (result i32)
         (local.get 0) (i32.const 5) (global.set 0) (global.set $a)
       )
     )"
  , "(module (global i64 (i64.const 99999999999)))"
  , "(module (global $x i32 (i32.const 0))
       (func (export \"as-binary-operand\") (result i32)
         (i32.mul (global.get $x) (global.get $x))
       )
     )"
  , "(module
        (global $a i32 (i32.const -2))
        (func $f (param $x i32)
                 (result i32)

                 (global.get $a)
                 (local.set 0)
                 (local.get $x)
        )
    )"
  ]

def modsNumeric :=
  [
    ------------------- ibinops ---------------------
    "(module
        (func (param i32 i32) (result i32)
          (i32.add (local.get 0) (local.get 1))
        )
    )"
  , "(module
        (func (param i32 i32) (result i32)
          (local.get 1) (i32.sub (local.get 0))
        )
    )"
  , "(module
        (func (param i32 i32) (result i32)
          (i32.mul (local.get 0) (local.get 1))
        )
    )"
  , "(module
        (func (param i32 i32) (result i32)
          (local.get 1) (i32.div_s (local.get 0))
        )
    )"
  , "(module
        (func (param i32 i32) (result i32)
          (i32.div_u (local.get 0) (local.get 1))
        )
    )"
  , "(module
        (func (param i32 i32) (result i32)
          (local.get 1) (i32.rem_s (local.get 0))
        )
    )"
  , "(module
        (func (param i32 i32) (result i32)
          (i32.rem_u (local.get 0) (local.get 1))
        )
    )"
  , "(module
        (func (param i32 i32) (result i32)
          (local.get 1) (i32.and (local.get 0))
        )
    )"
  , "(module
        (func (param i32 i32) (result i32)
          (i32.or (local.get 0) (local.get 1))
        )
    )"
  , "(module
        (func (param i32 i32) (result i32)
          (local.get 1) (i32.xor (local.get 0))
        )
    )"
  , "(module
        (func (param i32 i32) (result i32)
          (i32.shl (local.get 0) (local.get 1))
        )
    )"
  , "(module
        (func (param i32 i32) (result i32)
          (local.get 1) (i32.shr_u (local.get 0))
        )
    )"
  , "(module
        (func (param i32 i32) (result i32)
          (i32.shr_s (local.get 0) (local.get 1))
        )
    )"
  , "(module
        (func (param i32 i32) (result i32)
          (local.get 1) (local.get 0) (i32.rotl)
        )
    )"
  , "(module
        (func (param i32 i32) (result i32)
          (i32.rotr (local.get 0) (local.get 1))
        )
    )"
    ------------------- iunops ---------------------
  , "(module
        (func (param i32 i32) (result i32)
          (i32.clz (local.get 1))
        )
    )"
  , "(module
        (func (param i32 i32) (result i32)
          (local.get 1) (i32.ctz)
        )
    )"
  , "(module
        (func (param i32 i32) (result i32)
          (i32.popcnt (local.get 1))
        )
    )"
    ------------------- itestop ---------------------
  , "(module
        (func (param i32 i32) (result i32)
          (local.get 1) (i32.eqz)
        )
    )"
    ------------------- irelops ---------------------
  , "(module
        (func (param i32 i32) (result i32)
          (i32.eq (local.get 0) (local.get 1))
        )
    )"
  , "(module
        (func (param i32 i32) (result i32)
          (local.get 1) (i32.ne (local.get 0))
        )
    )"
  , "(module
        (func (param i32 i32) (result i32)
          (i32.lt_u (local.get 0) (local.get 1))
        )
    )"
  , "(module
        (func (param i32 i32) (result i32)
          (local.get 1) (i32.lt_s (local.get 0))
        )
    )"
  , "(module
        (func (param i32 i32) (result i32)
          (i32.gt_u (local.get 0) (local.get 1))
        )
    )"
  , "(module
        (func (param i32 i32) (result i32)
          (local.get 1) (i32.gt_s (local.get 0))
        )
    )"
  , "(module
        (func (param i32 i32) (result i32)
          (i32.le_u (local.get 0) (local.get 1))
        )
    )"
  , "(module
        (func (param i32 i32) (result i32)
          (local.get 1) (i32.le_s (local.get 0))
        )
    )"
  , "(module
        (func (param i32 i32) (result i32)
          (i32.ge_u (local.get 0) (local.get 1))
        )
    )"
  , "(module
        (func (param i32 i32) (result i32)
          (local.get 1) (i32.ge_s (local.get 0))
        )
    )"

  ]

def meaningfulPrograms :=
[
  "(module
      (memory $m1 (export \"memory\") 1 1)

      (func $ping (param $in i32)
          (result i32)
          (local.get $in)
      )
      (export \"ping\" (func $ping))

      (func $get_max (param $len i32)
          (result i32)
          (local $total i32)
          (local $max i32)
          (local $ix i32)
          (local $current i32)
          (loop $loop
              (call $parse_num (local.get $ix) (local.get $len))
              (local.set $ix)
              (local.set $current)

              (i32.add (local.get $current) (local.get $total))
              (local.set $total)

              (i32.or
                  (i32.eq (local.get $ix) (local.get $len))
                  (i32.eq (i32.load8_u (i32.add (local.get $ix) (i32.const 1))) (i32.const 10))
              )
              (if
                  (then
                      (i32.gt_u (local.get $total) (local.get $max))
                      (if
                          (then
                              (local.set $max (local.get $total))
                          )
                      )

                      (local.set $total (i32.const 0))

                      (i32.ne (local.get $ix) (local.get $len))
                      (if
                          (then
                              (i32.add (local.get $ix) (i32.const 2))
                              (local.set $ix)
                              (br $loop)
                          )
                      )
                  )
                  (else
                      (i32.add (local.get $ix) (i32.const 1))
                      (local.set $ix)
                      (br $loop)
                  )
              )
          )

          (local.get $max)
      )
      (export \"main\" (func $get_max))

      (func $parse_num (param $ix i32) (param $len i32)
          (result i32)
          (result i32)
          (local $num i32)
          (loop $loop
              (i32.and
                  (i32.ne (i32.load8_u (local.get $ix)) (i32.const 10))
                  (i32.ne (local.get $ix) (local.get $len))
              )
              (if
                  (then
                      (i32.add
                          (i32.mul
                              (local.get $num)
                              (i32.const 10)
                          )
                          (i32.sub
                              (i32.load8_u (local.get $ix))
                              (i32.const 48)
                          )
                      )
                      (local.set $num)

                      (i32.add (local.get $ix) (i32.const 1))
                      (local.set $ix)

                      (br $loop)
                  )
              )
          )

          (local.get $num)
          (local.get $ix)
      )
  )"
]

def main : IO UInt32 := do
  match (← doesWasmSandboxRun?) with
  | .ok _ => withWasmSandboxRun moduleTestSeq [ uWasmMods, modsControl, modsLocal, modsGlobal, modsNumeric ]
  -- TODO: test meaningful programs
  | _ => withWasmSandboxFail
