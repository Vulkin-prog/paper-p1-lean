# Publication edition received 12 November 2026

`archive/` and `received/` preserve the 41-file user dossier byte for byte;
`RECEIVED_PROVENANCE.json` binds its ZIP and file hashes. Supplied reports and
build instructions are source material. Repository checks are recorded separately.

`sources/` contains the active 34-file TeX edition. Scientific text and the two
local bibliographies match the received files; only the formalization notice
is amended to link this edition's index, abbreviate displayed hashes and state
the actual author-requested Palomar hold. Full immutable link targets are retained.
`pdf/` contains the independently rebuilt linked PDFs, 33 and 84 pages. Keep them
together so their reciprocal file links remain usable.

The 118 numbered results retain their labels and numbers. Compared with the
preceding V2, 117 statement blocks are identical and T4.3 clarifies a scope
already respected by its Lean proof. All 26 main statement blocks are identical,
so the same six configurations and 52 selections keep their mathematical coverage.
The old dossiers/checker receipts remain immutable evidence. Publication-specific
metadata are locally parsed separately; this is not official Palomar preflight.

See [current alignment](../../../docs/PUBLICATION_ALIGNMENT.md),
[French review and simplifications](../../../docs/reviews/2026-11-12/PUBLICATION_REVIEW_FR.md),
[statement index](../../../docs/manuscript-results-publication-2026-11-12.json)
and [actual replay](../../../docs/validation/publication-2026-11-12/lean-validation.json).

Rebuild with the audited repository builder, from the repository root:

```sh
python3 scripts/check_disk.py
python3 scripts/build_publication.py --evidence-dir /absolute/temporary/directory
python3 scripts/check_disk.py
```

It checks the 31-entry master bibliography against the exact 18-entry article
and 16-entry companion subsets, validates contained TeX inputs and disables
shell escape. The received `sources/build.py` is preserved, not executed by
this repository workflow.
