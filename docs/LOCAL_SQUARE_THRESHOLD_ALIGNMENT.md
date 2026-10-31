# Companion T9.1 and T9.2: local square exclusion and critical defects

**Status: both proved.** Coverage is 16 / 167: 8 / 73 main and 8 / 94
companion. Original locators: companion V1.6, page 39,
`companion_sections/pair_rigidity.tex:17` and `:62`, labels
`p13:rig:local-square` and `p13:rig:defective`. Their original statement
hashes and all manuscript bytes are preserved.

## T9.1: the exact finite offset set

`LocalSquareThreshold.companion_T9_1` uses an actual `Finset ℤ`, with positive
even cardinality m, contained in the integer interval [-B,B], B≥2. If the
natural integer base satisfies x>(B+1)^(12m), its translated product is not
an integer square. The condition already forces x>0.

`split_product_finset_bound` reindexes this set by `Fin (2*k)` using an
explicit equivalence. Distinctness follows from the finite set itself;
the offset bounds and complete translated product are transported exactly.
The internally proved degree-uniform T1.1 bound applies with U=x and R=B.

`local_square_threshold_sharp` proves the stronger exclusion threshold
x>(64B)^m. Positive m makes this threshold imply the required x≥2B.
`sixtyfour_mul_le_fifth_power` proves 64B≤(B+1)^5 for every B≥2, and
`local_square_threshold_power_five` gives x>(B+1)^(5m). Monotonicity then
gives the original exponent 12m.

This strengthens the finite conclusion; no analytic square-root branch,
tail estimate or polynomial-height bound is passed as a premise. All
arithmetic content used from T1.1 has already been proved. Improvement
`P1-MATH-0005` records the proposed threshold revision; no optimality is
claimed and no later asymptotic exponent is changed.

## T9.2: the literal kernel above 10B

`CriticalDefectPositions.criticalDefectivePositions x L` is exactly the
finite set of n in [x-1,x+L-1] whose actual large odd-prime kernel above
10(L+1) equals one. `criticalDefectivePositions_eq_interval` proves its
equality with the intrinsic defective set on [x-1,(x-1)+L]. Thus neither
the endpoint nor the B=L+1 convention is approximated.

`CriticalBandScale.critical_band_scale` supplies fixed positive constants
b=1/(2 log 2) and E=1/log 2+1 such that, beyond a C-dependent threshold,
every length in `|L-log N/log 2|≤C` satisfies

`b log N ≤ L+1 ≤ E log N`.

Every dyadic start x∈[N,2N), N≥2, has N/2≤x-1≤2N. The proved T1.3 local
count therefore applies with fixed base comparisons, H=10B and width L≤B.
`companion_T9_2` gives the manuscript's O_C(B/log B) bound uniformly before
all N, L and x. No regularity, admissibility or positive-probability
hypothesis is imposed on any start.

`uniform_critical_defect_constant` proves the stronger quantifier order

`∃ K>0, ∀ C, ∃ N₀(C), ∀ N≥N₀(C), ∀ L in the band, ∀ x∈[N,2N),`
`#criticalDefectivePositions ≤ K B/log B`.

The constant K is chosen from the fixed T1.3 comparisons before C; the
band-to-scale threshold is the only C-dependent choice. Improvement
`P1-MATH-0006` records this uniformity. A common threshold for all unbounded
C is not claimed.

## Validation

The project is compiled with Lean v4.36.0-rc2 and its pinned matching Mathlib.
The full source-identity checks, full build and actual 1,301-declaration kernel audit at the local-arithmetic checkpoint are run before publication. Only `propext`, `Classical.choice`
and `Quot.sound` are allowed. No new Paper C source, unproved literature
estimate or manuscript edit is introduced. Palomar remains a later milestone.
