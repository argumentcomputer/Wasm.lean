import Wasm

open Wasm
open System

def main (args : List String) : IO UInt32 := do
  try
    let file := FilePath.mk <| args.get! 0 
    let bin ← IO.FS.readBinFile file
    pure 0
  catch e =>
    IO.eprintln <| "Error: " ++ toString e -- avoid "uncaught exception: ..."
    pure 1

