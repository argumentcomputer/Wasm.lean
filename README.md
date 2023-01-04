# Wasm tools for lean

Included are:

* WAST -> Lean -> Binary parser.
* A Lean Webassembly runtime.
* [A Lurk Webassembly runtime](https://github.com/yatima-inc/Wasm.lean/tree/cognivore/2022-12-08/yatimise) via [Yatima language](https://github.com/yatima-inc/yatima-lang).
* Binary ouptuts are compatible with other Webassembly implementations.

![Visual representation of the previous list.](https://user-images.githubusercontent.com/66186054/210612265-32085aab-7463-4f0e-9d55-ebea0d805771.png)

## Lurk runtime demo

First we'll clone `cognivore/2022-12-08/yatimise` branch.

```bash
git fetch --all
git checkout cognivore/2022-12-08/yatimise 
```

Optionally, let's clean whatever possible artefacts and compiled dependencies. A poor person's reproducible builds.

```bash
lake clean
rm -rf lean_packages/*
```

Now let's `build` everything!

```
lake build
```

Awesome, now let's run the Wasm lean expression.

```
lake exe yati_raw
```

You should get a number as the result of this call.

Now build `lurk` and install it into a place in your `PATH`:

```
cd /tmp
git clone https://github.com/lurk-lang/lurk-rs.git
cd lurk-rs
git checkout 11a29cb723a49b442907cdeb1e09e6a5729742a7
cargo build
cargo install --path .
```

The install part installs binaries into `~/.cargo/bin`.

Do the same with `yatima-lang`:

```
cd /tmp
git clone https://github.com/yatima-inc/yatima-lang.git
cd yatima-lang
git checkout a6671e54b361e0f3d4c954803524762aee0f30f5
lake build
cp build/bin/yatima ~/.cargo/bin/
```

Now we can go back to the root directory of `Wasm.lean` project and run the following command:

```
yatima transpile Yati32Raw.lean -d=go -rs
```

This command tells the system that you want to run in Lurk function named `go` from the Lean file (!) called `Yati32Raw.lean`.

The last flag `-rs` means "use the reference Rust implementation of Lurk". Let's try out with our implementation!

```
yatima transpile Yati32Raw.lean -d=go -rs
```

As you see, all three times, the resulting number was the same. It has a special meaning, by the way, see if you can crack it!

If you could, send your answer to @cognivore over at Yatima Zulip to claim your bragging rights!

## Develop

`lake build`.

## Build

`lake build`.

## Test

Build `lspec`: `lake build lspec`.

Run tests with `./lean_packages/LSpec/build/bin/lspec`.
