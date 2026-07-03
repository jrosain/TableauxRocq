# Changelog

All new features and changes breaking the API from a prior version will be documented in this file.

## Current development version

### Breaking changes

- Extract `Term` and `Form` to GADTs.
  * theories/Prelude/Atoms.v: type is not carried in the `Atom` class anymore.  
	(isAtom): replaces `Atom`, has the same fields as `Atom` without the carrier.
  * theories/Syntax.v: Term and Form now take types and `isAtom` instances.  
	Leads to miscellaneous replacements throughout the code.

- Rename `SetOfNat` and `SetOfString`.
  * theories/Prelude/Sets.v: Renamed to `NSet` and `SSet` respectively.

- Extract concrete instances in their own files. Does not break the imports using Tableaux.All.  
  The imports using Tableaux.Core will not have access to the (unexported) instances anymore.
  * theories/Prelude/Sets.v: broken down into another file, named theories/Prelude/SetInstances.v
  * theories/Prelude/Atoms.v: broken down into another file, named theories/Prelude/AtomInstances.v
  * theories/Prelude/All.v: now also exports the instances.
  * theories/Prelude/Core.v: new file that exports everything except the instances.
  * theories/Syntax.v: broken down into another file, named theories/SyntaxInstance.v
  * theories/Skolemization.v: broken down into another file, named theories/SkolemizationInstances.v
  * theories/Proofs.v: broken down into another file, named theories/ProofInstance.v

### New features

- Extraction of the `CheckProof` function and parsing of TPTP style proofs. Yields an
  `OCaml` binary named `poulet`.
- Make TableauxRocq available as a nix flake (both the Rocq library and the fully
  certified proof checking software).

## Version 0.1 (Alpha Release for ITP 2026) - 29 April 2026

- First-order free-variable tableau calculus as a rewriting system between proof trees.
- Soundness proof w.r.t. its Tarski semantics.
- Proof-checking algorithm with good performances on big proofs and on
  (Skolemization-)optimized proofs.
