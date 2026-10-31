# The sharp prime-count input

**Status: proved.** Stable literature-input identifier: `P1-ARITH-PNT`.
This is a proved arithmetic input to article Lemma 2.1. The uniform
specialization and complete local-rigidity statement are now proved as well.

## Public P1 statements

`PaperP1.SharpPrimeCount.prime_counting_ratio_tendsto` proves the usual
sequential form

`(Nat.primeCounting B : ℝ) * log B / B → 1` as B→∞ through the naturals.

`PaperP1.SharpPrimeCount.primeCount_upper_eventually` proves that, for every
real η>0, there exists B₀≥2 such that every integer B≥B₀ satisfies

`primeCount B ≤ (1+η) * B / log B`.

The threshold precedes the variable cutoff. The inclusive convention p≤B is
identified exactly with `Nat.primeCounting`; there is no missing endpoint
prime. The real-to-natural floor conversion and the divisions by the positive
logarithm are proved. Neither declaration has a PNT premise.

## Recompiled analytic proof

The source is
[PrimeNumberTheoremAnd at the pinned commit](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/tree/127b50e33f6033e2147921167a117af96d9ba4ea),
Apache-2.0, originally using Lean 4.35.0 and Mathlib v4.35.0.
The [original licence](../third_party/PrimeNumberTheoremAnd/LICENSE) is preserved
and every adapted module carries provenance. The selected sources are:

| Upstream source | Git blob | Selected P1 scope |
|---|---|---|
| `PrimeNumberTheoremAnd/Sobolev.lean` | `1f98bcbccc7ba3b9c9ee02ec95404731085368f9` | Full mathematical content, split into `SobolevBasic`, `SobolevCS`, `SobolevTrunc`, `SobolevW1`, `SobolevW21` and `SobolevApproximation` |
| `PrimeNumberTheoremAnd/Fourier.lean` | `99e15a0237162df31161745e8e9e98a891c44a51` | Full mathematical content, `PNT/Fourier.lean` |
| `PrimeNumberTheoremAnd/SmoothExistence.lean` | `b33edf879b1117ae0912512529051f0ba77b7d9e` | Smooth interval cutoffs, `PNT/SmoothExistence.lean` |
| `PrimeNumberTheoremAnd/Mathlib/Algebra/Notation/Support.lean` | `13d3575b14d663481b15e0099f75c42739668f40` | Two support identities, `PNT/SupportHelpers.lean` |
| `PrimeNumberTheoremAnd/Mathlib/Analysis/Asymptotics/Asymptotics.lean` | `dc51688f7332e0caf3bd4d1b50c1d0052d304103` | Three constant-versus-identity estimates, `PNT/AsymptoticHelpers.lean`; old cast helpers replaced by current Mathlib facts |
| `PrimeNumberTheoremAnd/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean` | `1fa2d2b6a88a2b891dc7674914e8e3fa7d19472c` | Logarithmic-power limit, `PNT/LogGrowth.lean` |
| `PrimeNumberTheoremAnd/Wiener.lean` | `59fd5069a7eca51a8bc5005b5c43e31a5cbb38ac` | Through `WeakPNT`; unused bounded-variation block and all subsequent arithmetic-progression material excluded |
| `PrimeNumberTheoremAnd/Consequences.lean` | `d9283ccaac007eed83e131577df256bcecdd150f` | Through `pi_alt'`, `PNT/PrimeCountingAsymptotic.lean`; unused definitions and later prime-gap/Möbius results excluded |

The proof proceeds through smooth compactly supported functions, integrable
derivatives, Fourier estimates, approximation and the Wiener–Ikehara theorem
with an explicit Chebyshev-growth hypothesis. `PaperP1.PNT.WeakPNT` supplies
the von Mangoldt sum limit, using proved Mathlib nonvanishing and analytic
continuation results. `WeakPNT''` and `chebyshev_asymptotic` give the ψ and θ
forms. Partial summation then proves the actual inclusive prime-count
asymptotic `PaperP1.PNT.pi_alt'`. The public P1 wrappers derive the sequential
ratio and the exact one-sided uniform input.

## Selection and version changes

The upstream `prelim_decay_2` and `prelim_decay_3` contain unfinished proofs.
They and their only dependent `decay_alt` are excluded. The retained proof
instead uses the proved twice-differentiable Fourier identity and
`decay_bounds_key` on `W21`. None of the three excluded declarations is
referenced by the selected development. Architect blueprint annotations are
also excluded; the mathematical statements and proofs are ordinary Lean.

All selected declarations are compiled with `autoImplicit false`, as in the
source project, preventing an unknown name from becoming an extra implicit
premise. Lean 4.36 adaptations retain the statements: explicit root namespace
opens; qualified calls to newly namespaced helper methods; current
`natCast_atTop` lemmas; a redundant negation tactic replaced by interval
membership; and an explicit floor-of-negative-one simplification. The new
prime-count wrappers are P1 proofs.

Every selected theorem and lemma participates in the project-wide audit.
The initial PNT stage passed the complete build and actual axiom audit for
1,162 declarations, including 247 new declarations. The only kernel axioms
are `propext`, `Classical.choice` and `Quot.sound`; no unproved analytic
proposition is an assumption of PNT. The audit reader now handles apostrophes
inside Lean names; controls confirm acceptance of the complete actual output
and rejection of an unexpected axiom or a missing declaration.
The paper's local-rigidity thresholds and their uniform asymptotic
specialization are now proved, as recorded in
[LOCAL_RIGIDITY_ALIGNMENT.md](LOCAL_RIGIDITY_ALIGNMENT.md).

No change to an original manuscript statement or new mathematical correction
is asserted by this port.
