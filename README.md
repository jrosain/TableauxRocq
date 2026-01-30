# TableauxRocq: A Library of Free-Variable Tableaux in Rocq

This repository aims at providing a library for (i) formalizing free-variable tableaux
proofs in Rocq, and (ii) outputing *optimized* tableaux proofs for fast certification.

**Table of contents**

- [Installation and Local Compilation](#installation-and-local-compilation)
- [Outputing Proofs using TableauxRocq](#outputing-proofs-using-tableauxrocq)

## Installation and Local Compilation

### Requirements

This project can be compiled with Rocq 9.0.1 together with Rocq's latest stdlib release.
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
The `rocq-prover` package should provide both `rocq-core` and `rocq-stdlib`, so you should
be ready to go.

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
