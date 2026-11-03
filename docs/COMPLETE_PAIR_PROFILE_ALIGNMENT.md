# Complete pair profile: article Theorem 3.3

The theorem is **conditional**. All five displayed conclusions are proved
for the actual arithmetic and probabilistic quantities. The uniform geometric
properties described below are still explicit unproved arguments. This status
is separate from the 79 unconditionally completed numbered results.

The unchanged source is `manuscripts/paper-p1/v1.6/sources/main_sections/arithmetic.tex`.
Its positive and signed profiles sum over both orientations of strictly
separated pairs, with distance greater than L.

| Source display | Lean declaration | Exact scope |
| --- | --- | --- |
| `p1:arith:positiveprofile`, line 167 | `PositiveSeparatedSourceProfileUnderInputs.article_3_3_positive` | Actual `2^pairLoss-1`, all ordered separated dyadic pairs; whole finite `U_23` and `U_34`; error `N^(6/5+epsilon)` |
| `p1:arith:signedprofile`, line 170 | `SignedSeparatedSourceProfileUnderInputs.article_3_3_signed` | Actual affine compatibility indicator, full source rank including local kernels; whole finite `S_23` and `S_34`; same error |
| `p1:arith:cumulantexpansion`, line 173 | `ActualPairPhaseUnderInputs.article_3_3_cumulant` | Actual variance minus actual mean; nominal `lambda=N*2^(-L)`; error `N^(-4/5+epsilon)` |
| `p1:arith:leadingphase`, line 178 | `ActualPairPhaseUnderInputs.article_3_3_phases`, first conclusion | Printed residue-dependent constant and exponents; relative error tending uniformly to zero |
| `p1:arith:secondphase`, line 183 | `ActualPairPhaseUnderInputs.article_3_3_phases`, second conclusion | Entire finite `lambda^2/(3N)*S_23` removed; actual `L mod 4`; uniform relative error tending to zero |

All declaration names in this table have the prefix `PaperP1.`. Their latest
successful full build, direct kernel-axiom audit and declaration checks are
recorded in `manuscript-results.json` for main 3.3.

## Arithmetic and probability identities

`NormalizedPairRankLoss.pairLoss x y L` is literally
`2L-finrank(squareClassSpace x L + squareClassSpace y L)`.
It includes local kernels. It is not silently replaced by effective relative
nullity on irregular windows. `SourcePairKernelComparison.complete_rank_eq_loss`
identifies it with the actual complete relation-code dimension.

`SourcePairAffineWeight.eta_eq_compatibility` identifies eta with compatibility
of the actual finite affine start system. `joint_formula` proves the literal
joint probability identity, including incompatible pairs.

`CountVariance.second_cumulant_variance` identifies the full factorial cumulant
with Mathlib's variance of the actual infinite-model count minus its actual
Bochner expectation. L2 membership is proved from measurability and the finite
pointwise count bound. There is no moment hypothesis in this identity.

## Positive profile decomposition

The unsigned unit enumeration counts every nonzero even rational-unit relation,
including relations of incompatible pairs. Actual endpoint placements give the
exact orientation coefficient `2*(2a-b)/(ab)`, equal to `1/3` in both principal
channels. The actual private channel source mass has an unconditional error
`N^(1/2+1/b+epsilon)` from its whole finite unsigned main term.

The private principal families are disjoint and strictly separated. The
finite residual cover retains the separated height-one boundary, the height-two
endpoint boundary, both nonprivate principal populations, zero-unit alignments
and the high-channel tail. Their raw positive source masses are all proved
unconditionally, with the combined error `N^(6/5+epsilon)`. The support count
`N^(1+epsilon)` and full source-rank bounds provide the high-channel estimate.
The remaining nonaligned source mass uses the explicit geometric properties.

## Contacts and signed profile

The signed profile is first proved over all distinct ordered pairs using the
actual second factorial cumulant and exact nominal-centering identity. The
ordered close population is removed through its actual contact joint mass
and nominal squared mass. Its total absolute signed source weight is
`N^(1+epsilon)` unconditionally. Compatible exact contacts are retained in this
comparison; no claim that every close joint event has probability zero is used.

## Moving phases and subtraction

`PrincipalPairPhaseComparison.height_three` and `height_four` identify the
literal finite height sums with the two actual channel main terms.
`phase_three` and `phase_four` give the printed constants, with the actual
moving residues. `whole_first_channel` retains every term of `S_23`.

The existing phase equivalents hold uniformly over all sufficiently large
critical lengths. Positive phase lower bounds absorb the actual cumulant
error at exponent `-31/40`. The full finite 3:4 main term is negligible relative
to the first phase. The second comparison subtracts the exact 2:3 main term
before taking the ratio. `uniform_phases` proves positivity of both denominator
phases and both relative-error bounds for every positive tolerance. Its one
threshold precedes all critical lengths; the result is not restricted to
fixed-residue subsequences.

## Remaining geometric inputs

The ordinary theorem arguments are the already identified properties:

- `P1-GEO-NORMALIZED-CURVE-UNIFORM`: the uniform point bound for actual normalized
  prime curves with bounded positive Hilbert degree, including all recorded
  primary-theorem and scheme/degree/chart translations.
- `P1-GEO-ORDINARY-SURFACE-COVER`: the finite curve and point cover on actual
  ordinary source surfaces, including the recorded projection, lifting and
  degree translations.
- `P1-GEO-CHOSEN-SOURCE-SURFACE-COVER`: the distinct cover for the actual chosen
  Veronese source embedding and its height-one source curves.

The positive-profile theorem selects finite embedding and coordinate caps
before these arguments, with component cap `sizeCap(epsilon/64)`. The signed,
cumulant and phase component theorems expose their own finite caps at fixed
density `1/100`. Their separately selected caps and quantifier order are kept
in the public declarations; no target profile or remainder is supplied as input.
See `LITERATURE_INPUTS.md` for exact primary sources and unproved translations.

There are no added axioms, `sorry`, `admit`, or unchecked computation proofs.
The original V1.6 source bytes are preserved. Palomar submission remains deferred.
