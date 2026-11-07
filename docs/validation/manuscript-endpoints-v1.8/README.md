# Proof-entry review provenance

The [complete index](../../manuscript-endpoints-v1.8.json) binds each of the
167 v1.8 numbered TeX results to one or more exact Lean theorem interfaces.
There are 261 distinct theorem interfaces and three separate mathematical
definitions. A conjunction may need several interfaces to retain every printed
clause, sign, finite identity or inherited hypothesis.

The original complete extraction is under [compiled](compiled/compiled-types-validation.json).
It ran against proof source `08f019df4d33a817377e5c937356fe4d87ae08e1` with
Lean v4.36.0-rc2 and exited zero. Its
[latest replay](../checkpoint-1003/endpoint-replay.json) at source
`3df7615af2aa6a2a2bc6856bd4203c401d0434de` recompiled all 264 types
byte-identically. All 261 propositions were audited; only
`propext`, `Classical.choice` and `Quot.sound` occur. The complete source-bound
[project replay](../checkpoint-1003/validation.json) separately preserves all
18,627 build jobs, 19,984 axiom reports and 19,907 reference checks.
It includes the nine new concrete irregular-window certificates, which
are explanatory examples and do not change the 167-result theorem selection.

The frozen review inputs in [review-input-scope](review-input-scope) are the
historical 536-type extraction used while reading the statements. They are
not the terminal theorem selection and include conditional intermediate
interfaces. Some complements were only source-read at that time. Every
interface selected by the final 167-result index is now actually compiled in
the current 264-type extraction (261 proofs plus three definitions).

The original review partition was disjoint: 79 canonical-result comparisons
and nine targeted dense/counting comparisons by the separate review instance,
and 79 other comparisons by the parent. The separate instance has now also
[directly compared those remaining 79 results](../../reviews/2026-11-07/endpoint-remaining79.json),
including their 118 distinct compiled interfaces. The checker binds every
reviewed block, type, source hash and required clause to the current index.
Thus all 167 labels have independent comparison records across the reports'
stated snapshots. The earlier parent notes remain preserved. The eight
theorems in the replica and homogeneous-mass modules were also separately read.
Reports and their exact source snapshots remain frozen under
[reviews/2026-11-07](../../reviews/2026-11-07).

Run `python3 scripts/check_manuscript_endpoints.py` from the repository root.
The checker first verifies the v1.8 and earlier manuscript integrity records,
then the source/type/review bindings, complete-replay receipts and log hashes.
The current proof-source manifest also binds `lakefile.toml`, so a build
configuration change invalidates its source snapshot just like a changed
compiler pin, dependency lock or Lean proof source.
The [controls](controls.json) use altered in-memory copies to verify rejection
of an omitted result, a missing 15.11 clause, a changed 15.4 context, an erased
15.13 printed premise, a type-digest change, and a definition counted as proof.
The expanded eleven-case control set also checks the current scope-replay
digest, completed independent coverage, separate example review and the
injective ordered-list domain in7.2. No actual source is changed by these controls.

These records distinguish kernel checks from the AI-assisted comparison of
TeX meanings and Lean types. They do not claim an automatic semantic proof
of that translation, independent human peer review or Palomar registration.
All six Palomar dossiers remain on hold at the user's request.
