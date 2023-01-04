# Wasm tools for lean

Included are:

* WAST -> Lean -> Binary parser.
* A Lean Webassembly runtime.
* [A Lurk Webassembly runtime](https://github.com/yatima-inc/Wasm.lean/tree/cognivore/2022-12-08/yatimise) via [Yatima language](https://github.com/yatima-inc/yatima-lang).
* Binary ouptuts are compatible with other Webassembly implementations.

![Visual representation of the previous list.](https://user-images.githubusercontent.com/66186054/210612265-32085aab-7463-4f0e-9d55-ebea0d805771.png)

## Develop

`lake build`.

## Build

`lake build`.

## Test

Build `lspec`: `lake build lspec`.

Run tests with `./lean_packages/LSpec/build/bin/lspec`.
