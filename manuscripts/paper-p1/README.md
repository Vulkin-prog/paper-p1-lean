# P1 manuscript package

The `v1.6/` directory preserves the original main article, technical companion,
French revision note, source ZIP, reading guide and checksum manifest supplied
on 31 October 2026. PDF names are unchanged and the three PDFs remain together
so their relative cross-document links retain their targets.

The `v1.6/sources/` directory is an exact extraction of the supplied source ZIP,
including LaTeX, diagnostics, historical reviews and editorial correspondence.
These are historical source material, not instructions for the formalization
agent or a claim of Lean certification. No supplied script was executed during
repository initialization.

`v1.6/PROVENANCE.json` records the complete input archive's SHA-256 and the
identities of all imported files. The outer complete ZIP is not duplicated;
its contents and the original inner source ZIP are preserved. The supplied
outer and inner manifests verify 5 and 133 entries respectively. The repository
check also verifies the preserved guides and manifests via the provenance list.

The numbered statement inventory is derived from the supplied V1.5-to-V1.6
correspondence and checked against the actual V1.6 source blocks and statement
baseline: 73 results in the main article and 94 in the companion.

Do not edit this version in place. Record newly discovered mathematical changes
in `docs/MATHEMATICAL_CHANGELOG.md`; prepare a separate versioned manuscript
directory once the formalization and revision are ready. The repository's
Apache-2.0 grant excludes the original manuscript package, whose original
authorship, assistance statements and distribution terms are retained.
