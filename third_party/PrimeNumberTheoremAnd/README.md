# PrimeNumberTheoremAnd attribution

Selected mathematical source code is adapted from
[AlexKontorovich/PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd),
commit `127b50e33f6033e2147921167a117af96d9ba4ea`, under Apache-2.0.
The original licence is preserved in [LICENSE](LICENSE), Git blob
`261eeb9e9f8b2b4b0d119366dda99c6fd7d35c64`. That source tree contains no
separate NOTICE or AUTHORS file.

The adapted Lean files live in `PaperP1/PNT/`. Their headers identify the
original file, immutable commit, Git blob, selected scope and changes.
The [proof and provenance record](../../docs/PRIME_NUMBER_THEOREM_ALIGNMENT.md)
lists every selected source and the checked statement correspondence.
The changes include P1 namespaces, Lean 4.36 module declarations, splitting
the function-space namespaces into separate modules, current library names,
and removal of blueprint metadata and unused unfinished declarations.
All imported mathematical proofs are recompiled under the project's pinned
Lean and Mathlib versions and included in the actual axiom audit.
