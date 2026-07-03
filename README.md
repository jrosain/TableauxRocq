# TableauxRocq: A Library of Free-Variable Tableaux in Rocq

This repository aims at providing a library for (i) formalizing free-variable tableaux
proofs in Rocq, and (ii) outputing *optimized* tableaux proofs for fast certification.

**Table of contents**

- [Documentation](#documentation)
- [Installation and Local Compilation](#installation-and-local-compilation)
- [Outputing Proofs using TableauxRocq](#outputing-proofs-using-tableauxrocq)

## Documentation

Documentation gets automatically deployed for each version of `TableauxRocq`. The
documentation following the development version (e.g., tracking the `master` branch)
can be accessed at [jrosain.github.io/TableauxRocq/master](https://jrosain.github.io/TableauxRocq/master/).  
Documentation for a specific version is linked on the associated `release/` branch.

## Installation and Local Compilation

### Requirements

This project depends on Rocq. It is compiled using Rocq 9.1.1 in the CI, but is compatible
with the following versions of Rocq:
- `rocq-core 9.0.0` with `rocq-stdlib 9.0.0`
- `rocq-core 9.0.1` with `rocq-stdlib 9.0.0`
- `rocq-core 9.1.0` with `rocq-stdlib 9.1.0`
- `rocq-core 9.1.1` with `rocq-stdlib 9.1.0`

There are two ways of compiling the project.

#### Nix Installation (recommended)

A fully-reproducible setup is achieved using `flake.nix` and `shell.nix` files and a
pinned version of `nixpkgs`. We ensure that the project always compiles under this pinned
version of Rocq. One simply needs to use `nix-shell` to fetch and install the correct
version of Rocq.

The library is available using Nix flakes. It can be added to the inputs using the following lines:
```
tr = {
  url = "git+https://github.com/jrosain/TableauxRocq";
  inputs.nixpkgs.follows = "nixpkgs";
};
```
The corresponding output is in `tr.packages.${system}.rocqPackages.rocq-tableaux`. We currently support the systems `x86_64-linux` and `aarch64-linux`.

#### opam Installation

Another way of installing the dependencies of the project is via `opam`, using one of the pairs listed above.
For instance, if one wants the latest compatible version of Rocq, they have to enter the following commands:
```
opam pin add rocq-core 9.1.1
opam pin add rocq-stdlib 9.1.0
```
`ocamlfind` is also necessary but should be already installed.

### Compilation

After installing the dependencies, the following command configures and compiles the project:
```
make
```
In order to use the library globally on your computer, you can `install` it:
```
make install
```

If you are a developer of the library and simply want to configure (i.e., generate or
re-generate the `Makefile`s), you can use the `config` target:
```
make config
```

### Documentation

The documentation can be generated via the `doc` target of the Makefile:
```
make doc
```
*Warning*: this commands needs `pandoc` to generate the index file out of the
`README.md`. Note that it is included in the `nix` configuration file, so if you use nix,
it should work out of the box.

## Outputing Proofs using TableauxRocq

If you develop a tableau-based automated theorem prover, you can certify your proofs using
TableauxRocq. TableauxRocq's core is based on a minimal syntax and proof system, but we
provide an extended syntax, semantics and tableau proofs in the
[ExtendedSyntax](theories/ExtendedSyntax.v) file, that supports the full first-order syntax. Then,
to get started on developing an output, a showcase of the different types of rules are
done in the following files:

- [drinker](examples/drinker.v): a proof of the drinker paradox $\exists x.\ P(x) \to
  \forall y.\ P(y)$ using two different Skolemization methods: inner and outer
  Skolemization. This illustrates how to use a formula multiple times, and how inner
  Skolemization is better than outer Skolemization.
- [branching](examples/branching.v): a proof of the formula $\exists x.\ P(x) \to P(a)
  \land P(b)$. Here, both the inner and outer Skolemization proofs are also showcased even
  though they have the same number of rules applied. Nevertheless, this gives a nice
  example of a branching rule.

The folder [devtools/tests](devtools/tests) has examples for the application of other
rules, but these files are not documented.
