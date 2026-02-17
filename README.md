# TableauxRocq Source Code

This folder contains the `Rocq` source code for the paper:

*TableauxRocq: A Deep Embedding of Free-Variable Tableaux in Rocq*.

**Table of contents**

- [Installation and Local Compilation](#installation-and-local-compilation)
- [Browsing the Code](#browsing-the-code)

## Installation and Local Compilation

### Requirements

This project can be compiled with Rocq 9.0.1 together with Rocq's latest Stdlib release.
There are two ways of installing it.

#### Nix Installation (recommended)

A fully-reproducible setup is achieved using a `shell.nix` file and a pinned version of
`nixpkgs`. We ensure that the project always compiles under this version of Rocq. Hence,
one simply needs to input `nix-shell` to fetch and install the right version of Rocq.

#### opam Installation

Another way of installing the dependencies of the project is via `opam`:
```
opam pin add rocq-prover 9.0.1
```
The `rocq-prover` package provides both `rocq-core` and `rocq-stdlib`, so you should
be ready to go.

### Compilation

After installing the dependencies, the following command configures and compiles the project:
```
make
```
We expect this command to be quite fast: it takes between one and two minutes on our laptops.  
In order to use the library globally on your computer, you can `install` it:
```
make install
```

If you want to configure (i.e., generate or re-generate the `Makefile`s), you can use the
`config` target:
```
make config
```

### Documentation

The documentation can be automatically generated via the `doc` target of the Makefile:
```
make doc
```
*Warning*: this commands needs `pandoc` to generate the index file out of the
`README.md`. Note that it is included in the `nix` configuration file, so if you use nix,
it should work out of the box.

## Browsing the Code

The notations we provide throughout the code are in plain ASCII. When browsing in the
generated HTML or for users of emacs+proof-general, they will be automatically prettified
to their unicode counterpart. The prettified symbols are listed below.

- `\to` $\leadsto$ `→`
- `\in` $\leadsto$ `∈`
- `\subseteq` $\leadsto$ `⊆`
- `|=` $\leadsto$ `⊧`
- `[[` $\leadsto$ `〚`
- `]]` $\leadsto$ `〛`
- `Gamma` $\leadsto$ `Γ`
- `sigma` $\leadsto$ `σ`
- `rho` $\leadsto$ `ρ`
- `mu` $\leadsto$ `μ`
- `Bot` $\leadsto$ `⊥`
- `Neg` $\leadsto$ `¬`
- `\union` $\leadsto$ `∪`
- `\inter` $\leadsto$ `∩`
- `\equiv` $\leadsto$ `≡`
- `|>` $\leadsto$ `▷`

Most of the paper (and of the development) focuses on the files
[Semantics](theories/Semantics.v), [Skolemization](theories/Skolemization.v),
[Proofs](theories/Proofs.v), and [Checker](theories/Checker.v).

The management of sets and locally nameless classes can be found in the
[Prelude](theories/Prelude/All.v).  The correspondance lemmas between the fragment and
extended syntax are in the [ExtendedSyntax](theories/ExtendedSyntax.v) file.
