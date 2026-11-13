# Uniform event bounds, Hermite laws and the fixed-moment barrier

This contained project is the final, merged remainder of the publication
formalization. It aims at **five public registrations in total**, within the
author's limit of six. The four issued entries and the complete `RegistryV2`
project are preserved byte for byte. This candidate does not amend them.

The mathematical question is quantitative Poisson approximation for long runs
of a random multiplicative function. The proof needs control over subfamilies
whose cardinality can grow with the scale. A finite collection of moment
estimates cannot supply that control. Three selected compound statements expose
the event calculus, the resulting positive approximations and this obstruction.

| Selected statement | Mathematical content | Direct printed coverage |
| --- | --- | --- |
| `PaperP1Registry.Final.Affine.uniform_event_calculus` | The exact centered expansion; arithmetic Fourier representation; homogeneous envelope uniform over all subfamilies at one scale threshold; compatible nullity; unique direct component partition and factorization; weighted full-support counts summed over all cardinalities, with one threshold before every subset and minimum size. Generic expansion and partition identities are auxiliary parts of this calculus. | Main2.1–2.5; companion13.1 |
| `PaperP1Registry.Final.Reference.positive_hermite_approximation` | Actual single/double-jump Poisson laws approximate the arithmetic run count: exact-parameter error at most N^(-4/3+ε), and fixed-height sharp moving total-variation equivalents. The exact quadratic positivity interval and singleton formula calibrate this positive-reference family. | Main7.1,8.4 |
| `PaperP1Registry.Final.Obstruction.fixed_moment_barrier` | Explicit normalized positive perturbations match every factorial moment except their perturbation order, have exact total variation and uniformly bounded exponential moments. With order floor√logN, each fixed factorial moment eventually agrees exactly, while total variation exceeds every N^(-γ). | Companion Proposition15.1 and its displayed, unnumbered sequence corollary |

The thirteen main-result clauses from the two earlier unregistered scopes are
retained in full: the first eight fields of the first target and all five in
the second. The first target's ninth field directly adds companion13.1.
[The clause map](clause-map.json) gives the exact inherited types and field
numbers; [the final allocation](../palomar/REGISTRATION_PLAN_FINAL.json) maps
all26 main results to the unchanged four records and this candidate. Its42
selected statements are39 already published declarations plus these three
compound targets. Statement counts therefore differ from counts of printed
results and of conjunction clauses.

The uniform full-support count retains regular local rank and strict pairwise
separation greater than L. Its threshold precedes every subset and minimum
support size; the sum covers all cardinalities up to the subset's size. It
requires neither primitivity nor affine compatibility, and asserts the saturated
exponent2−ε rather than the endpoint2.

The moment-obstruction construction is a separate family of probability laws, with
**no claimed multiplicative realization**. It shows the insufficiency of fixed
moments plus exponential-moment control for polynomial rates; it is not a
lower bound for the actual arithmetic run law. The Hermite equivalent fixes
the height before the threshold, and the exact-parameter Hermite result asserts
an upper bound only. No new exact-Hermite lower bound is claimed. Main5.2 keeps
its printed254-order conditional premise in its existing published record.

These results concern probabilistic number theory, quantitative Poisson
approximation and dependent rare events. Classical finite-difference and
quadratic-mass identities are used explicitly as supporting tools. The scope
does not claim that those identities are new, or that all92 companion results
are directly selected for registration.

`ChallengeP1FinalFoundations.lean` is a literal Mathlib-only statement surface;
its three intentional holes are not proof evidence. The Solution imports only
the substantive parent proof development and canonical libraries. Literal
models precede proof elaboration in both files. Its111 theorem declarations,
including all three selected targets and the model-transport bridges, are
listed in `audit-declarations.json` and checked by `AuditRegistryFinal.lean`.
Lean remains **v4.36.0-rc2**, with the same pinned Mathlib revision and parent
path dependency. Paper C reuse and its Apache-2.0 attribution remain documented
in [PAPER_C_REUSE.md](../docs/PAPER_C_REUSE.md).

Reproduction from the repository root:

```sh
python3 scripts/check_registry_final.py
lake -d RegistryFinal build ChallengeP1FinalFoundations SolutionP1FinalFoundations AuditRegistryFinal
lake -d RegistryFinal env lean RegistryFinal/AuditRegistryFinal.lean > registry-final-axioms.txt
python3 scripts/check_registry_final.py --audit-log registry-final-axioms.txt
```

The local audit and kernel comparison are distinct from the new official full
preflight, Palomar verification, rendered Challenge, editorial review and issued
record. Only actual public records count as completed registrations in
[`CYCLE_STATE.json`](../palomar/publication/CYCLE_STATE.json).
