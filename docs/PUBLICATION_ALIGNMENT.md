# Publication alignment, 12 November 2026

The active publication dossier contains 118 numbered results: 26 main and 92
companion. All labels and result numbers are preserved. Compared with the
preceding V2, 117 statement blocks are identical and T4.3 explicitly separates
the homogeneous conditional/propagation clauses from the actual-run small-contact
mass. The existing theorem `FixedSourcePropagationTheorem.main_6_3` already
proves those scopes. No Lean mathematical source or pin is changed.

- [Current source/type correspondence](manuscript-results-publication-2026-11-12.json).
- [Immutable correspondence snapshot](validation/publication-2026-11-12/documentary-snapshot.json).
- [French critical review](reviews/2026-11-12/PUBLICATION_REVIEW_FR.md).
- [Fresh build, axiom and compiled-type evidence](validation/publication-2026-11-12/lean-validation.json).
- [Received archive and active sources/PDFs](../manuscripts/paper-p1/publication-2026-11-12/).
- [Final Palomar allocation](../palomar/REGISTRATION_PLAN_FINAL.json) and
  [preserved six-candidate preparation](../palomar/REGISTRATION_PLAN_PUBLICATION.json).
- [Metadata-only official-parser checks](validation/publication-2026-11-12/publication-metadata-validation.json).
- [PDF layout and link verification](validation/publication-2026-11-12/pdf/visual-review.json).

The received 41-file ZIP and supplied reports are preserved separately from
our own checks. T7.1's direct physical-witness proof and T12.4's dependency
account match the existing formal development. The 10:12:15 phase calculation
clarifies an existing companion calculation, without asserting a full cumulant
equivalent. The reference table retains the distinction between exact quadratic
optimality and the exact-Hermite upper bound.

The earlier six-candidate allocation uses the `RegistryV2` project and52 selected
declarations. Its source files and qualification evidence stay unchanged. Four
of those scopes are now issued public records. At the author's request the two
unregistered remainders are merged in the separate `RegistryFinal` project, with
direct companion13.1 and15.1 selections and the latter's displayed corollary.
The [final allocation](../palomar/REGISTRATION_PLAN_FINAL.json) aims at five total
records and42 selections, covering all26 main results explicitly. The new
three-target interface has its own111-theorem audit and requires a fresh full
official workflow; none of the four published entries is reopened. See the
[detailed correspondence](REGISTRATION_FINAL_ALIGNMENT.md). The final caller is
`palomar-final-preflight.yml`; earlier callers and receipts remain preserved.

The frozen preparation records describe the earlier author-requested hold;
they are not live submission state. The author subsequently resumed the six
cycles and explicitly confirmed the responsible-author/maintainer relationship
for source `f9a2d213265a6833318745dd7f2d74c02090ab19`. The first official full
preflight and Palomar's own verification both passed;
[current public progress](../palomar/publication/CYCLE_STATE.json)
records this separately. The author later explicitly authorized publication
of favorable actual reviews without repeated approval prompts. Each review is
examined and presented before its exact digest is registered; blocking findings
are assessed and justified corrections precede a new submission.

Reproduction:

```sh
python3 scripts/check_publication.py
python3 -m unittest discover -s tests -p test_publication.py
python3 scripts/build_publication.py --evidence-dir /absolute/temporary/directory
```

The original V2 correspondence and qualification remain available under their
historical paths. The paper's statement correspondence is an AI-assisted
source/type review, not a machine translation of TeX or independent human review.
