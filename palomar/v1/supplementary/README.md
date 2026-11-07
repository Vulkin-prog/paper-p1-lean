# Supplementary local verification

These records supplement the immutable standard Comparator receipts. They are
local checks, separate from Palomar's complete reusable workflow, source
provenance audit, editorial review, intake and registration.

- [Three-kernel replays](three-kernel-replays.json): eleven families, 44 selected
  declarations; Lean, NanoDa and con-ron `--verified --jobs=2` accepted every
  solution. Each family records its exact source commit, selection, unchanged
  standard configuration hash, binary identities and original compressed log.
  The source commits differ; no replay is silently attributed to a later tree.
- [Kernel controls](kernel-controls.json): each checker accepted the positive
  control and rejected a well-formed export with a deliberately ill-typed
  proof. The six recorded process codes belong to Comparator. NanoDa's native
  rejection process, for example, exits 101 while Comparator exits 1. Both
  original exports and the simple standalone control source are retained.
- [Optional verifier controls](optional-kernel-controls.json): Lean paranoid,
  lean4lean and con-leche each accepted the positive export and rejected the
  ill-typed export. These six additional local controls are separate from
  the pinned Palomar profile and from any candidate replay.
- [Metadata shapes](metadata-shapes.json): eleven metadata files passed the
  community v0.4 schema and the official metadata minimum parser pinned at
  PalomarSubmission 14aa8d6b3c2f14a8540605e37144560b9a00e7e7. This does not
  provide or infer a human relationship declaration.
- [Historical source layout](source-layout.json): immutable source footprint,
  root licence, submodule/LFS-pointer and materialized lockfile checks at its
  recorded source. Remote canonical provenance and licensee classification
  remain tasks for the complete workflow.

All comparisons retained bubblewrap isolation. No checker was switched to a
trusted mode, and no submission configuration contains `external_kernels`.
Derived local configurations merely enabled the supplementary con-ron replay.
The kernel declaration counts include imported dependencies; they are not
counts of manuscript results. Revised manuscript coverage remains 167/167.
