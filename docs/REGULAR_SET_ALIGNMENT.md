# Article Proposition 3.1: the regular set

**Status: proved**, all clauses of main Proposition 3.1. Coverage is 11 / 167:
8 / 73 main and 3 / 94 companion. Original locator: V1.6 main article,
page 14, `p1:arith:core`, `main_sections/arithmetic.tex:49`. Its proof is in
the companion's Section `p14:comp:regular-transfer`. Original bytes and the
statement hash in the coverage ledger are unchanged.

## The actual regular and exceptional sets

`RegularStarts.regularStarts N L` is exactly

`{x ∈ [N,2N) : finrank(squareClassSpace x L) = L}`.

`irregularStarts` is its complement inside this interval. The effective space
is the image of even selections of the full vertex window `[x-1,x+L-1]`,
with every prime parity retained. No compatible or positive-probability
filter is substituted for rank regularity.

`TwoDefectsInRelation.nonzero_relation_has_two_defects` proves that every
nonzero even relation uses two distinct actual B-defective vertices. Private
large prime coordinates force all nondefective coefficients to vanish;
the zero coordinate sum excludes a singleton support. Here B=L+1.
`irregularStarts_subset_twoDefectWindows` then places the whole exceptional
set in the exact two-defect window set already counted in companion T1.3.

`RegularSetAsymptotic.irregular_count_critical` proves, for every fixed C
and ε>0, one N₀ before all N≥N₀ and all lengths in
`|L-log N/log 2|≤C`, the literal bound `#irregularStarts ≤ N^ε`.
This is the manuscript's `N^o(1)` assertion.

## Arbitrary affine targets, including incompatible windows

`RegularAffineBounds.affineWindowMass x L b` is the actual infinite-measure
probability that the full relative-bit system has target `b : Fin L → F₂`.
The zero target is not privileged. Exact finite-cylinder transfer identifies
this probability with the actual affine fiber mass.

On a regular window, `affine_atom_on_regular` proves that every target has
mass p=2^(-L). In a critical-band window the proved local rigidity gives
relation rank at most one. `affineWindowMass_zero_or_rank` retains the
incompatible case with mass zero; otherwise the mass is the inverse power
of two at the actual effective rank. Thus its deviation from p is at most p
and its mass is at most 2p, without a positivity assumption.

`affine_marginal_sum_critical` gives exactly

`sum_{x in A} |P(A_x X=b_x)-p| ≤ p N^ε`

for every deterministic A⊆[N,2N) and every family of targets. The threshold
is chosen before A, the targets and the run length.

## Laws, coupling and both means

`CountObservables.countMoment G L j` is the actual Bochner expectation of
the jth power of the count on G under the infinite prime-sign measure.
`restrictedCountLaw_realizes` identifies the finite coefficient law with
the full pushforward by that count. No finite-model approximation remains.

`lawTotalVariation` uses the probability convention: half the ordinary
sum of absolute singleton differences. `count_law_total_variation_eq`
proves that it is literally half the sum of differences of the actual
infinite count probabilities, over the finite common support [0,N].
This fixes the factor-of-two convention explicitly.

`count_law_subset_coupling` bounds this distance by the actual probability
that the full and restricted counts disagree on the same prime signs.
That probability is at most the sum of active discarded-start probabilities,
hence at most `2p #irregularStarts`.

`mean_regular` gives `E Z_regular = p #regularStarts`, while
`regular_mean_bias` gives its exact bias `p #irregularStarts` from λ=Np.
`full_mean_bias` bounds the full-count bias by the same quantity, using all
exact marginals. Consequently `regular_set_finite_transfer` proves

`TV + |E Z-λ| + |E Z_regular-λ| ≤ 4p #irregularStarts`.

`regular_set_transfer` combines this with the exceptional count and the
critical-band inequality `p≤2^C/N`, giving the explicit bound

`(4 * 2^C) * N^(-1+ε)`.

## Conditional fixed moments and second factorial cumulants

The source explicitly assumes uniformly bounded fixed moments for this
clause. That premise is retained, rather than inferred from coupling alone.
`FiniteMomentTransfer.ordered_moment_difference_bound` proves, for q≥j
and R>0 on a common finite sample with 0≤W≤Z,

`|E Z^j-E W^j| ≤ R^j P(Z≠W) + E Z^q / R^(q-j)`.

This is an elementary deterministic truncation proof. For fixed j and ε,
choose a positive integer s with j/s≤ε/2, put q=j+s and R=N^(1/s), and use
the proved disagreement bound with exponent ε/2. The higher moment order
is chosen before N, never allowed to grow with N.

`regular_moment_transfer_on` allows an arbitrary deterministic family of
lengths. `regular_moment_transfer_along` needs moment bounds only along one
prescribed sequence L(N); it assumes no bound at other lengths. Both prove
the stated `O(N^(-1+ε))` difference for every fixed positive j. The uniform
critical-band version is `regular_moment_transfer`.

`secondFactorialCumulant` is exactly
`E[Z(Z-1)]-(E Z)^2 = E Z^2-E Z-(E Z)^2`.
`factorial_second_moment_eq` and `secondFactorialCumulant_eq` prove this
identity under the actual infinite measure, including the diagonal term.
The corresponding `_on`, uniform and `_along` cumulant-transfer theorems
give the same error exponent from the moment bounds and the bounded mean.

This completes the conditional assertion of Proposition 3.1. It does not
claim that the model's uniform fixed-moment bounds have already been proved;
that remains the separate result main 6.4.

## Validation and mathematical record

Lean v4.36.0-rc2 and the pinned matching Mathlib are used. All new proofs are
included in the generated audit. Full build, source identities and the actual
kernel axiom audit are checked before publication. The project contains
1,289 audited theorem/lemma declarations, distinct from numbered coverage.
No additional Paper C port or unproved literature input is introduced.
No new mathematical correction is identified in this proposition. The four
confirmed improvements remain tracked separately. No Palomar entry is made.
