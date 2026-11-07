# Proof-entry review provenance

The [complete index](../../manuscript-endpoints-v1.8.json) binds each of the
167 v1.8 numbered TeX results to one or more exact Lean theorem interfaces.
There are 261 distinct theorem interfaces and three separate mathematical
definitions. A conjunction may need several interfaces to retain every printed
clause, sign, finite identity or inherited hypothesis.

The actual current extraction is under [compiled](compiled/compiled-types-validation.json).
It ran against proof source `08f019df4d33a817377e5c937356fe4d87ae08e1` with
Lean v4.36.0-rc2 and exited zero. All 261 propositions were audited; only
`propext`, `Classical.choice` and `Quot.sound` occur. The complete source-bound
[project replay](../checkpoint-1002/validation.json) separately preserves all
18,625 build jobs, 19,975 axiom reports and 19,898 reference checks.

The frozen review inputs in [review-input-scope](review-input-scope) are the
historical 536-type extraction used while reading the statements. They are
not the terminal theorem selection and include conditional intermediate
interfaces. Some complements were only source-read at that time. Every
interface selected by the final 167-result index is now actually compiled in
the current 264-type extraction (261 proofs plus three definitions).

The recorded review partition is disjoint: 79 canonical-result comparisons
and nine targeted dense/counting comparisons by the separate review instance,
and 79 other comparisons by the parent. The new eight theorems in the replica
and homogeneous-mass modules were subsequently read by the separate instance.
Reports and their exact source snapshots remain frozen under
[reviews/2026-11-07](../../reviews/2026-11-07).

Run `python3 scripts/check_manuscript_endpoints.py` from the repository root.
The checker first verifies the v1.8 and earlier manuscript integrity records,
then the source/type/review bindings, complete-replay receipts and log hashes.
The [controls](controls.json) use altered in-memory copies to verify rejection
of an omitted result, a missing 15.11 clause, a changed 15.4 context, an erased
15.13 printed premise, a type-digest change, and a definition counted as proof.

These records distinguish kernel checks from the AI-assisted comparison of
TeX meanings and Lean types. They do not claim an automatic semantic proof
of that translation, independent human peer review or Palomar registration.
All six Palomar dossiers remain on hold at the user's request.
