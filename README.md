# P1 — Lean formalization

Formalization project for **Sharp Poisson approximation and second-order
correction for long multiplicative runs**, main article and technical companion,
by **Brice Pouly**, working version **1.6, 31 October 2026**.

**Status: active formalization, 24 / 167 numbered results proved.**
Article Lemma 5.1, the full first-excluded-prefix polynomial identity, is proved
over any commutative semiring. Auxiliary lemmas develop the finite centering
transform at orders zero, one and two. The principal Poisson asymptotic theorems remain open.
Article Proposition 4.1 is proved on an arbitrary probability space with a
finite measurable indicator family. The actual count law is identified as a
measure; coefficients are Bochner expectations; zero-marginal sites are removed
without changing the law; complementary Bernoulli products are probabilities.
Article Proposition 5.2 is proved with its exact positive remainder kernel,
joint activation mass and ordinary ℓ¹ norm bound, without an independence
assumption between the prefix and suffix.
Actual finite-cylinder run marginals are proved to be zero in incompatible
cases and inverse powers of two at the effective rank otherwise. The
full-support centered Fourier formula and its sharper nullity bound are proved
on effective dual spaces and instantiated for actual run moments. Exact
finite-cylinder consistency is proved for the infinite prime-sign measure,
including its full count law and centered moments. Effective square-class
images and their relative relation kernels are identified with the actual
character spaces, completing Lemma 4.2. Its
[alignment note](docs/FOURIER_ALIGNMENT.md) records the representation and scope.
Lemma 4.3 is proved with its compatible-nullity bound, comparison and equality
case, using exact actual joint masses and retaining the empty family. See its
[alignment note](docs/COMPATIBLE_NULLITY_ALIGNMENT.md).
Lemma 4.4 is proved with the unique finest direct partition, exact factorization
of joint and centered moments, and additivity of effective relative nullity
under the actual infinite measure. See its
[alignment note](docs/DIRECT_COMPONENT_ALIGNMENT.md).
Companion Lemma T1.1 is proved with the exact degree-uniform bound
`U ≤ (64R)^d`, including real radii and integer bases. The proof uses formal
series, coefficient cancellation and integer-square separation. See its
[alignment note](docs/SPLIT_PRODUCT_ALIGNMENT.md).
Companion Lemma T1.2 is proved as an actual positive-solution count, uniformly
over every coefficient in a fixed real polynomial box. Both square and
nonsquare coefficient products are included, and all divisor, ideal and
unit estimates used in the proof are proved. See its
[alignment note](docs/QUADRATIC_COUNT_ALIGNMENT.md).
Companion Lemma T1.3 is proved in full: the uniform local `O(B/log B)`
bound, global `N^(1/2+o(1))` count, exact dyadic two-defect-window `N^o(1)`
count, and fixed real affine interval versions. The complete statements use
one common threshold and include the literal `B=L+1` convention. See
[statement alignment](docs/DEFECT_COUNTS_ALIGNMENT.md).
Article Lemma 2.1 is proved in full: exact Griesmer inequality, general and
critical rank thresholds, and exact subcritical independence of actual
relative signs under the infinite model. The critical-band effective ranks,
p or 2p marginals and a uniform pointwise O(1/N) bound are also proved.
The lower base bound U≥aN suffices, and one threshold controls every shorter
window. See [local rigidity alignment](docs/LOCAL_RIGIDITY_ALIGNMENT.md).
Article Proposition 3.1 is proved: the full-rank regular set has only
`N^o(1)` exceptional windows; the actual count laws, both means and arbitrary
affine marginal sums have the stated transfer estimates. Fixed-moment and
second factorial-cumulant transfers retain the source's bounded-moments
hypothesis, including the case of one prescribed length sequence. See
[regular-set alignment](docs/REGULAR_SET_ALIGNMENT.md).
Companion Lemmas T9.1 and T9.2 are proved for the exact integer offset sets
and critical vertex windows. Their proofs give a stronger local square
threshold and an absolute constant in the defect bound, with separate entries
in the mathematical change log. See
[local-square and critical-defect alignment](docs/LOCAL_SQUARE_THRESHOLD_ALIGNMENT.md).
Companion T22.2 is proved with both its missing-block inequality and its
sum over arbitrary ordered distinct tuple families. Falling-factorial moments
are actual infinite-model expectations. The proof also gives an exact
heterogeneous-marginal version. See
[missing-block alignment](docs/MISSING_BLOCK_ALIGNMENT.md).
Companion T19.1 is proved for every N≥2 and L≥1: the exact support is
bounded by `ceil(N/L)`, and every factorial moment belongs to the literal
`j! * p^j` nonnegative integer lattice, including all irregular windows.
See [support and lattice alignment](docs/SUPPORT_LATTICE_ALIGNMENT.md).
Companion T9.3 is proved: the actual number of free components is within
O(B/log B) of the pair intersection dimension, with exact cutoff 10B and
B=L+1. Complete relations and the small-prime/parity rank cost are proved;
overlapping windows, component selection and both-block membership are included.
See [free-component alignment](docs/FREE_COMPONENT_ALIGNMENT.md).
Companion T9.4 is proved with the exact bivariate factor-height constant,
including the integer quotient. The primitive-factor hypothesis is unnecessary.
See [factor-height alignment](docs/BIVARIATE_FACTOR_HEIGHT_ALIGNMENT.md).
Article Lemma 8.1 is proved for the actual quadratic Poisson signed measure:
all singleton masses and the exact closed positivity interval, in both
directions, are included. See [positivity alignment](docs/QUADRATIC_POISSON_ALIGNMENT.md).
Companion T19.12 is proved for arbitrary finite measurable indicator families:
the signed Palm residual bound, exact heterogeneous coefficients, and the
equal-marginal specialization retain all cancellations and zero-marginal
conventions. See [signed Palm alignment](docs/SIGNED_PALM_ALIGNMENT.md).
Companion T19.13 is proved for arbitrary probability laws, including laws
without a first moment. The weighted recurrence criterion and parameter
stability retain the original constants, with weaker parameter hypotheses.
See [weighted recurrence alignment](docs/WEIGHTED_POISSON_NORM_ALIGNMENT.md).
Companion T2.1 is proved uniformly in the position of every integer window:
its logarithmic small-prime budget and exceptional-value count have explicit
absolute constants. See [small-prime alignment](docs/SMALL_PRIME_BUDGET_ALIGNMENT.md).
Companion T20.2 is proved for the full product tail of positive integers,
with one constant per exponent and every real cutoff T>=1. See
[integer product-tail alignment](docs/INTEGER_PRODUCT_TAIL_ALIGNMENT.md).
Companion T2.2 is proved with the exact selected-coordinate codimension,
simultaneous multiplicity and unordered-decomposition bounds, and no further
dimension loss on removing zero coordinates. See
[coordinate regularisation alignment](docs/COORDINATE_REGULARISATION_ALIGNMENT.md).
Companion T23.1 is proved with actual positive probability laws, the exact
factorial-moment perturbation and total variation constant, and uniform
exponential-moment control. Its parameter interval also extends to [0,2],
with the zero perturbation at the final endpoint made explicit. See
[moment-obstruction alignment](docs/MOMENT_OBSTRUCTION_ALIGNMENT.md).
The following unnumbered asymptotic example is also proved, including the
literal floor, fixed-order moment identities and failure of every polynomial
rate. See [its alignment](docs/MOMENT_OBSTRUCTION_ASYMPTOTICS.md).
The sharp PNT input is proved by a selected, recompiled and audited analytic
development, with [separate provenance](docs/PRIME_NUMBER_THEOREM_ALIGNMENT.md).

| Material | Location |
|---|---|
| Main article | [PDF](manuscripts/paper-p1/v1.6/P1_V1_6_Main_Article_2026-10-31_EN.pdf) |
| Technical companion | [PDF](manuscripts/paper-p1/v1.6/P1_V1_6_Technical_Companion_2026-10-31_EN.pdf) |
| French revision note | [PDF](manuscripts/paper-p1/v1.6/P1_V1_6_Revision_Note_2026-10-31_FR.pdf) |
| Original archives, editable sources and identities | [Manuscript package](manuscripts/paper-p1/README.md) |
| Coverage of all 167 numbered results | [Source-to-Lean correspondence](docs/MANUSCRIPT_ALIGNMENT.md) |
| Corrections and mathematical improvements | [Mathematical change log](docs/MATHEMATICAL_CHANGELOG.md) |
| Formalization state and next steps | [Status](docs/FORMALIZATION_STATUS.md) |
| Paper C reuse candidates | [Reuse record](docs/PAPER_C_REUSE.md) |
| Future Palomar registrations | [Preparation](docs/PALOMAR_PLAN.md) |

## Reproducible environment

Lean is pinned to **v4.36.0-rc2**. Mathlib is pinned to commit
`9d581dfff2e41de989072ea63abf3daf69311520`, tagged `v4.36.0-rc2`,
whose toolchain matches. The dependency lock file records all transitive revisions.

```sh
python3 scripts/check_disk.py
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
python3 scripts/cache_dependencies.py
python3 scripts/check_disk.py
python3 scripts/check_sources.py
python3 scripts/update_audit.py --check
lake build
lake env lean Audit.lean
```

Use the committed lock file for ordinary builds; `lake update` is needed when
initially resolving or intentionally updating dependencies. Cache downloads are
restricted to the project's actual imports and their transitive dependencies. Set
`XDG_CACHE_HOME`, `MATHLIB_CACHE_DIR` and `TMPDIR` to local Ubuntu directories if
their defaults point elsewhere. Available-space warnings start at 10 GiB; large
downloads must stop below 5 GiB. See [environment policy](docs/ENVIRONMENT.md).

`lake build` treats Lean warnings as errors. The audit generator checks coverage
of every project theorem and lemma. `Audit.lean` exposes the kernel
axioms of each selected proved declaration. A successful build verifies only
the checked declarations, not the unformalized manuscript claims. The source
integrity check verifies file identities and the coverage inventory; it does
not certify mathematical proofs.

## Scope and attribution

The target includes exact marginals and square-class spaces, affine and stopped
expansions, arithmetic estimates, scalar reconstruction and optimality,
rational-channel refinements and the companion's additional results. External
mathematical inputs will be individually tracked rather than hidden as axioms.

The project follows the traceability approach of
[paper-c-lean](https://github.com/Vulkin-prog/paper-c-lean). No Paper C Lean code
was imported at initialization. Parity vectors, the prime-sign model and
selected arithmetic counting proofs have since been adapted and rebuilt.
The reuse record identifies every source and adaptation. Its old compiled
files are not reusable under this compiler.
Palomar registrations are planned after completion and
qualification; no registration exists for this project yet.

New Lean code, project scripts and project documentation are licensed under
[Apache-2.0](LICENSE), following Paper C. The unchanged manuscript package is
excluded from that grant and retains its original authorship and terms; no new
manuscript licence is inferred. The source package records its original AI
assistance. Repository setup and initial development are agent-assisted;
compilation and source checks are distinct from independent human review.
