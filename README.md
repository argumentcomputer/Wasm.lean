# Wasm tools lite for lean

Webassembly tools implemented in Lean.

Uses Straume's Zeptoparsec instead of Megaparsec to reduce the amount of dependencies and make compilation to other languages easier.

To get the reference test suite, please run:

```
git submodule update --init --recursive
```

## Develop

`lake build`.

## Building

`lake build`.

## Tests

Build `lspec`: `lake build lspec`.

Run tests with `./lean_packages/LSpec/build/bin/lspec`.
