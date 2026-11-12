# P1 V2 — six Palomar dossiers

The current plan covers **all 26 numbered results of the main V2.0 article**,
including every clause recorded in its source/type correspondence. It uses
**six registrations and 52 compared theorem declarations**. The technical
companion supplies the substantive proofs; this does not claim that all 92
companion results are separately selected for registration.

| Group | Dossier | Main results | Compared statements |
|---|---|---|---:|
|1|Affine events and homogeneous envelopes|2.1–2.5|8|
|2|Stopping and complete-law reconstruction|4.1–4.2,5.1–5.3|8|
|3|Arithmetic pairs and fixed channel heights|3.1–3.2,8.1–8.3|13|
|4|Cumulants and quadratic optimality|3.3–3.4,6.1–6.2|8|
|5|Quadratic approximation and Poisson scales|1.1–1.2,7.2–7.4|10|
|6|Quadratic positivity and Hermite laws|7.1,8.4|5|

The recommended submission sequence starts with **dossier 5**, the central
optimal quadratic theorem and its consequences, then 4, 3, 2, 6, 1. This puts the
main research conclusions before the supporting algebra. It changes neither
the limit of six registrations nor the logical coverage allocation shown above.

The affine dossier includes more than a generic finite-field identity: its
common homogeneous envelope controls original incompatible events and exact
heterogeneous weights, with one critical-band threshold for **all** subfamilies,
including growing cardinality. The explicit2^card factor is retained. This is
the uniform arithmetic/probabilistic control used by the stopped reconstruction.
The canonical factorization specifies exactly when disconnected components
can be multiplied. The cumulant, pair-profile and law-approximation dossiers
then expose the sharp powers and moving phases for the full original count.

The [machine-readable allocation](../palomar/REGISTRATION_PLAN_V2.json) links
each printed label and statement hash to its compared theorem bundle and parent
proof endpoints. The [clause review](../palomar/v3/COVERAGE.md) spells out the 26 bundles and inherited context. Coverage means a selected explicit statement, not merely a
result imported somewhere in a proof. Multiple clauses can require several
selections. The third and fourth cumulant identities are useful additional
selected foundations in dossier 4.

Each Challenge imports only canonical Mathlib and defines its mathematical
objects literally. Only its selected statements have deliberate proof holes.
Its Solution imports the substantive parent development, reproduces the same
literal models and proves explicit bridges to the existing theorems. Solutions
never import a Challenge. Definitions precede proof elaboration in both modules:
this keeps generated proof constants identical for Comparator's structural
comparison, rather than relying on mere definitional equivalence.

This is a contained Lean project with a path dependency on `..`, the substantive
P1 development in the same repository. Its compiler and all Git dependency pins
match the parent. No separate proof repository, new mathematical assumption,
new compiler version or full second Mathlib download is needed. The repository
root licence applies. Paper C reuse remains attributed in module documentation
and [the precise reuse record](../docs/PAPER_C_REUSE.md).

The exact mean is retained where the article uses it. The nominal mean is used
only in its specified references. The conditional transfer theorem explicitly
requires all 254 fixed orders 3 through 256. Fixed channel heights and polynomial
weights precede their scale thresholds; no uniformity in a growing height is
asserted. Zero marginals are admitted in the homogeneous envelope and canonical
factorization; positivity is retained where the Fourier and compatible-nullity
statements require it on the admissible index set. No matching lower bound for
the exact-parameter Hermite reference is asserted.

Brice Pouly and ORCID [0009-0008-8491-2467](https://orcid.org/0009-0008-8491-2467)
are together in every dossier's author, responsible-maintainer and source-author
records under `palomar/v3/`. These use Palomar's documented compatible structured
person form so that the identifier is an actual person field.

The [local validation record](../palomar/v3/VALIDATION.json) is separate from the
complete official reusable Palomar workflow, intake, editorial review and
registration. The active [manual preflight](../.github/workflows/palomar-preflight.yml)
selects one of these six dossiers and requires an exact commit and an explicitly
confirmed personal authorization relationship. **No cycle is launched by CI.**
Finish or close one entire cycle before starting another. Publication of a
private review requires the user's separate decision after receiving that review.

The old17 component interfaces and old six-dossier/68-selection plan remain
preserved as historical evidence. These six V2 dossiers replace the old planned
scopes; they are not six additional filings. No historical receipt is silently
reused as evidence for these new selections.

Reproduction, from the repository root after building the parent development.
Reuse its dependency directory once, as CI does, to avoid a second dependency
checkout or cache download:

```sh
mkdir -p RegistryV2/.lake
ln -s ../../.lake/packages RegistryV2/.lake/packages
```

Keep an existing `RegistryV2/.lake/packages` directory or link; the setup above
is only for a fresh contained-project build. Then run:

```sh
python3 scripts/check_disk.py
python3 scripts/check_registry_v2.py
lake -d RegistryV2 build
lake -d RegistryV2 build ChallengeP1V2AffineEvents ChallengeP1V2StoppingReconstruction ChallengeP1V2PairsChannels ChallengeP1V2CumulantsOptimality ChallengeP1V2QuadraticLimits ChallengeP1V2ProbabilityReferences
lake -d RegistryV2 env lean RegistryV2/AuditRegistryV2.lean > registry-v2-axioms.txt
python3 scripts/check_registry_v2.py --audit-log registry-v2-axioms.txt
python3 -m unittest discover -s tests -p test_registry_v2.py
python3 scripts/check_disk.py
```

`AuditRegistryV2.lean` checks all 262 proved interface and bridge theorems. Its
inventory is reconstructed by the read-only guard. The parent audit continues
to cover its 20019 mathematical and historical interface declarations separately.
The actual compiled-type extractor and its 52-name input are preserved under
`palomar/v3/evidence/`; the local validation record gives their hashes and the
command and environment needed to repeat the extraction with a temporary file.
