# Integrity of the reviewed editorial previews

The automatic workflow now checks all three preserved simplification previews,
in addition to the existing frozen-v1.8 source and proof-entry checks.
Run these independent checks from the repository root:

```sh
python3 scripts/check_manuscript_endpoints.py
python3 scripts/check_editorial_previews.py
python3 -m unittest discover -s tests -p test_editorial_previews.py -v
```

The [actual validation record](validation.json) binds the checker and control
sources to their completed executions. No Lean source, mathematical ledger
entry, manuscript source, PDF or frozen review is changed by this addition.

## Exact scope

The checker reconstructs all four patches in memory: the five initial
clarifications and the three simplification passes. It accepts exact contexts
and offsets only. It then compares all 48 scientific files at each stage with
the independent review's preimage/image hashes and its complete source manifest.
The delivered copies allow only the actual preview dates, footers, metadata
and cross-PDF filenames in the three root files. Arbitrary preamble or input
changes cannot be disguised as presentation edits.

All 167 result identities are retained. The first two simplification passes
change no numbered block after the clarification stage; the third explicitly
clarifies distinctness in 7.2 and the fixed-height cutoff in T1.9. The four
removed labels are exactly the unused internal equations of the former T4.3
proof, with no remaining reference or reassignment. Every retained reference
must resolve. The source map keeps each current result's file, line, statement
hash, printed number and complete existing proof bundle, including all clauses
of T22.7 rather than its nominal formula alone.

The delivered PDF hashes are bound to their successful build and completed
visual-review records. Page counts, all six successful LaTeX executions,
the separate structural metadata-only follow-up, cross-file targets and
compressed raw logs must remain consistent. The three published final receipts
are pinned as immutable capsules; a future manuscript revision receives a new
capsule rather than rewriting the archived evidence.

The two targeted compiled snapshots contain 35 declaration records: 34 audited
propositions and one separate conclusion definition. Their inventories, actual
exit files, complete axiom logs and the independently read types are checked.
Only `propext`, `Classical.choice` and `Quot.sound` are permitted. A definition
cannot be counted as a theorem. The live Lean files must still have the exact
reviewed bytes and declaration locations.

These compiled snapshots belong to proof source
`7bfc953cd6092eebfbae5f24aeb72b7180693537`. A newer documentary or proof-index
header does not turn them into a fresh replay. The existing complete manuscript
gate remains responsible for the current proof-source/replay bindings. The
editorial checker assesses exact evidence integrity; mathematical meaning is
assessed in the frozen AI-assisted reviews. It executes no compiler, PDF
renderer, dependency download or official Palomar workflow.

## Controls

The 29 controls comprise three positive cases and 26 intentional failures.
All mutations occur only in memory. The positive cases verify the actual
capsules, an equivalently serialized scope snapshot, and preservation of a
historical snapshot's identity when only a newer documentary header is supplied.
That last case does not validate the hypothetical new header's complete proof
replay; the separate manuscript gate has that responsibility.

The negative cases cover missing or altered results, loss of the autonomous
compressed proof, omission of the two scope conventions, arbitrary preamble
changes, changed PDF bytes, rewritten final receipts, loss of the propagation
and moment interfaces of T22.7, changed result numbers or source locations,
and omitted or falsely attributed simplification proposals.

Additional scope controls first recompute the file hashes, then test the
substantive gates: missing declarations, changed compiled types, a definition
misclassified as a theorem, a nonstandard axiom, an incomplete axiom log,
failed extraction, contradictory exit files and inflated receipt counts.
Thus these controls exercise more than detection of stale checksums.
The patch parser also rejects fuzzy contexts, escaped/unknown paths, incorrect
hunk counts and out-of-range hunks.

The latest source/PDF preview remains 64/101 pages with all 13 identified
simplifications applied. All earlier snapshots remain preserved. Palomar
submissions remain on hold, with the same six dossiers and 68 selections.
