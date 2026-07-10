# Grammar of the Certified Parser

`TableauxRocq` is extracted to a certified proof checker in `OCaml`. In order to make it
easily compatible to automated theorem provers, it parses a variant of [TPTP](tptp.org)
and [SC-TPTP](https://jcailler.github.io/assets/pdf/cade30.pdf). This file describes the
grammar that the checker accepts.

The grammar mostly relies on [TPTP's
BNF](https://tptp.org/UserDocs/TPTPLanguage/SyntaxBNF.html). It currently only supports
`fof` directives.

## Problem Declaration

The order of the declarations is not important, but we start by explaining how to declare
the problem that has been solved. The conjecture that must be shown can be declared using
one of the two roles `conjecture` and `negated_conjecture`:
```
fof(drinker, conjecture, ? [X] : (! [Y] : (d(X) => d(Y)))).
fof(drinker, negated_conjecture, ~ (? [X] : (! [Y] : (d(X) => d(Y))))).
```
There can be only one conjecture. If a proof uses axioms, one can declare them with the eponymous role:
```
fof(drink, axiom, ? [X] : d(X)).
```
Of course, axioms can be given directly in the conjectures:
```
fof(drinker, conjecture, (? [X] : d(X)) => ? [X] : (! [Y] : (d(X) => d(Y)))).
fof(drinker, negated_conjecture, (? [X] : d(X)) & ~(? [X] : (! [Y] : (d(X) => d(Y))))).
```
We advise to declare the axioms separately: the checker's algorithm takes a list of
formulas as input, so it can handle axioms natively.

## Local Definitions

The parser supports local definition of formulas, using the eponymous role:
```
fof(drinker, definition, ? [X] : (! [Y] : (d(X) => d(Y)))).
```
These definitions can be referred to later, e.g., when defining the conjecture:
```
fof(drinker_conj, negated_conjecture, ~ drinker).
```
Beware: do not override the name of any 0-ary predicates.

## Proof Steps

TableauxRocq's proofs are a bit different from the usual sequents in the TPTP language. In
TableauxRocq, we do not care about the current state of the sequent, but only on the rule
applied on which formula. Consequently, the syntax differs slightly from the one of a
`fof_sequent`. Hence, an inference step has the following shape:
```
fof(<name>, plain, <target formula>, inference(<rule name>, <children list>, <optional term>)).
```
Note that, for a closure rule, there can be multiple target formula or no target
formula. The syntax is slightly different in this case:
```
fof(<name>, plain, <formula list>, inference(<rule name>)).
```
The following rule names are supported:
 | Rule name      | In SC-TPTP? |
 |----------------|-------------|
 | leftFalse      | yes         |
 | leftNotTrue    | no          |
 | leftHyp        | yes         |
 | leftNotNot     | yes         |
 | leftAnd        | yes         |
 | leftNotOr      | yes         |
 | leftNotImplies | yes         |
 | leftOr         | yes         |
 | leftImplies    | yes         |
 | leftNotAnd     | yes         |
 | leftIff        | yes         |
 | leftNotIff     | yes         |
 | leftExists     | yes         |
 | leftNotAll     | yes         |
 | leftForall     | yes         |
 | leftNotEx      | yes         |

The prefix `left` can be left out, i.e., we also support the rules `false`, `notTrue`,
`notNot`, etc. It is here for compatibility with SC-TPTP.

The only rules creating the optional term are `leftExists`, `leftNotAll`, `leftForall` and
`leftNotEx`. The first two expect a Skolem symbol `f(X, Y, Z)` and the last two expect a
"free" variable `X`.

The final piece that is needed is the substitution, associating free variables to actual
terms. It can be declared (only once in the file) using the `substitution` role as follows.
```
fof(s, substitution, { X1 -> t1 ; ... ; Xn -> tn }).
```
If a free-variable of the proof does not appear in the substitution, it will stay as
itself. This field is not mandatory, i.e., if a tableau can be closed without
substitution, one does not need to add an empty substitution declaration.

### Children Order for Beta-Rules

Consider the following proof-step:
```
fof(s, plain, Φ, inference(r, [s1, s2])).
```
Then, depending on Φ and `r`, the following formulas are added in the contexts of `s1` and `s2`:
| Φ          | `r`         | `s1`   | `s2`  |
|------------|-------------|--------|-------|
| F or G     | leftOr      | F      | G     |
| ~(F & G)   | leftNotAnd  | ~F     | ~G    |
| F => G     | leftImplies | ~F     | G     |
| F <=> G    | leftIff     | ~F, ~G | F, G  |
| ~(F <=> G) | leftNotIff  | F, ~G  | ~G, F |

## Full Example

### Drinker (Outer Skolemization)

```
fof(drinker, definition, ? [X] : (d(X) => ! [Y] : d(Y))).
fof(drinker, negated_conjecture, ~drinker).

fof(s, substitution, { Y -> f(X) }).

fof(s0, plain, ~drinker, inference(leftNotEx, [s1], $fot(X))).
fof(s1, plain, ~(d(X) => ! [Y] : d(Y)), inference(leftNotImplies, [s2])).
fof(s2, plain, ~(! [Y] : d(Y)), inference(leftNotAll, [s3], $fot(f(X)))).
fof(s3, plain, ~drinker, inference(leftNotEx, [s4], $fot(Y))).
fof(s4, plain, ~(d(f(X)) => ! [Y] : d(Y)), inference(leftNotImplies, [s5])).
fof(s5, plain, [d(Y), ~d(f(X))], inference(leftHyp, [])).
```

### Drinker (Inner Skolemization)

```
fof(drinker, definition, ? [X] : (d(X) => ! [Y] : d(Y))).
fof(drinker, negated_conjecture, ~drinker).

fof(s, substitution, { X -> c }).

fof(s0, plain, ~drinker, inference(leftNotEx, [s1], $fot(X))).
fof(s1, plain, ~(d(X) => ! [Y] : d(Y)), inference(leftNotImplies, [s2])).
fof(s2, plain, ~(! [Y] : d(Y)), inference(leftNotAll, [s3], $fot(c))).
fof(s3, plain, [d(X), ~d(c)], inference(leftHyp, [])).
```
