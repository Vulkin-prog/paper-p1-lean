# Palomar preparation

The revised version 1.7 inventory is now **167/167 proved**, after full
checkpoint P1-MATH-0984 at proof commit
27bc1758cb8ed6b2a95add0f70f90dfe450c2de7. The original v1.6 inventory retains
the two false-original statuses. The revised sources, both inspected PDFs,
and their separate statement ledger are committed.

Current official tooling was checked on 7 November 2026:

- Comparator is integrated into Lean from 4.35 onward. The pinned 4.36.0-rc2
  toolchain provides `lake comparator`, its matching exporter, Lean's checker
  and bundled NanoDa. The old Paper C tool binaries are not reused.
- The current PalomarSubmission revision is
  14aa8d6b3c2f14a8540605e37144560b9a00e7e7; its toolchain minimum is
  v4.35.0-rc2. The current PalomarPolicy revision is
  28bd48b9b71bbb2a82c718ce761d5a4220ef8e60.
- Every submitted Lean source must use the module system and have at most
  10,000 lines. The old 19,294-line generated audit was replaced by a compact
  command over a separate JSON inventory. The new command invokes Lean's own
  `#print axioms` for exactly the same 19,288 source-discovered theorems.
  A full build and direct audit passed; missing output and a forbidden axiom
  were rejected in negative checks. See axiom-audit-validation.json.
- The local source scan is `python3 scripts/check_palomar_sources.py`.
  It is a bounded-purpose preparation check, not the full reusable Palomar
  workflow required before intake.

The first selected family, ordinary smooth integers in logarithmic intervals,
now has a standalone 95-line Mathlib-only Challenge, matched Solution and
metadata. Its three selected statements passed Comparator and both Lean and
NanoDa at source commit eb3039966bdeeb0b4e5e895bc3bbecfe4222342a with the
bubblewrap boundary enabled. The invocation is `lake env lake comparator` so
that the exact toolchain's bundled NanoDa is on the executable search path.
Its receipt and compressed logs are in palomar/v1/smooth_windows and
palomar/v1/evidence. The complete build passed 18,537 jobs and the extended
audit checked 19,291 substantive and Solution theorems.

Further independently meaningful families and the complete pinned reusable
workflow remain to be prepared and qualified. Local compilation and dual-kernel
replay do not establish registry acceptance or registration.

The second family, prescribed squarefree kernels of shifted split products,
has four selected declarations and passed the isolated comparison, Lean and
NanoDa at c85100fb3371cfe2869cf98e2fb8e54eed9a231c. It includes the actual
counting bounds, corrected capped comparison, exact nonnegative-parameter
criterion, and actual arbitrarily large counterexamples to the original
unqualified comparison. Its full project build passed 18,541 jobs and the
extended audit checked 19,299 theorems. Its receipt and original compressed
logs are in palomar/v1/quadratic_kernels and palomar/v1/evidence.

Registrations are planned **after formalization is complete**, as requested.
There are no submitted records, generated registry IDs, qualified Comparator
configurations or certification claims at initialization.

Use Paper C's separation of checked solutions, standalone challenges, selected
declarations and per-family metadata as a reference. The family split is not
fixed yet; derive it from completed coverage rather than guessed counts.

Before a submission:

1. Complete and review source-to-Lean alignment for both documents, explicitly
   listing all unproved literature inputs and mathematical changes.
2. Freeze source identities, all dependency revisions and a full commit SHA;
   rebuild from the committed lock file and inspect kernel axioms.
3. Check actual Comparator, NanoDa and Palomar compatibility with Lean
   v4.36.0-rc2. The old Paper C pipeline used 4.34.0; compatibility is not assumed.
4. Prepare independently meaningful statement interfaces, matched solutions,
   exact declaration selections, and metadata with authorship, sources, scope,
   limitations and the validated commit.
5. Run the appropriate statement comparison and kernel replays, preserve their
   logs and distinguish local qualification from registry verification/editorial
   decisions. Record actual registration identifiers only after issuance.

Do not invent publication identifiers for the supplied working manuscript.

The third and fourth families, asymmetric parity-space profiles and optimal
quadratic Poisson–Charlier approximation, passed the isolated statement
comparison and both kernels at source commit
3b777fec1dc58fb209b48c4e8e15d0de1fcd51c3. Their 3 and 4 selections bring the
local total to 14 in four families. The full build passed 18,545 jobs and
19,317 source-discovered theorem axiom checks. Exact receipts and compressed
logs are committed beside each family. The probability model, both-sign run
starts, actual mean and cumulant, sharp upper and lower powers, quadratic
normalization and exact probability criterion are explicit in the standalone
optimal-quadratic interface. The asymmetric interface retains the corrected
matching radius, full exponential loss, old-bit invariance and checked
counterexample to the radius-one printed version.
