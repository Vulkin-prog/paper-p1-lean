# Uniform aligned residual rank — partial companion T1.9

Source: companion T1.9, page 14, `p1:arith:alignedrank`,
`companion_sections/arithmetic_appendix.tex:770`, statement hash
`7de9608ecc780ef5a448579b04b2ebeabe5e1157579ce3025b0303a047157acc`.
The final fixed-height assertion with an enlarged prime cutoff remains
open; T1.9 is **in progress**, not counted complete. Original manuscript
bytes are unchanged.

## Actual finite value kernel

`FiniteResidualRank.valueKernel S` is the kernel of the full prime-parity
map on the deduplicated finite set S. This is an actual linear map on
actual integers, with every prime coordinate retained.

For a true subset S of the union of a*[Ux,Ux+Rx] and b*[Uy,Uy+Ry],
omit P={primes <=H} union primeFactors(a*b), where H>=Rx,Ry. Every
remaining prime row meets at most two distinct values. The graph and
pins are built from those literal row supports. Each free component
has a nonempty value set, and distinct component value sets are disjoint.
The prime-parity sum of one free component vanishes outside P.

For a positive integer component cutoff K and coding radius t>=1,
write r=|P|. If S lies in [U,U+R], R>=1, 2R<=U and

    (64R)^(2Kt) < U,

then `TwoProgressionResidualRank.finite_rank_bound` proves

    rank(valueKernel S)
      < max(r+1, 2t*2^((r+1)/t+1)) + |S|/(K+1).

Both quotients on this finite right side are natural-number quotients.
The inequality holds for the true subset; an enclosing interval is used
only to bound the size of the actual distinct integers.

## Checked Runge--code--graph chain

1. A binary coefficient word selects the union of its actual component
   value sets. Disjointness gives the exact prime-parity and total-parity
   equations. The appended row is the **component size modulo two**,
   rather than an unjustified constant one.
2. A nonzero kernel word selects a nonempty even set with square product.
   The proved degree-uniform Runge lemma excludes at most 2Kt selected
   values. Since each component has at most K values, its coefficient
   weight exceeds 2t.
3. The exact finite Hamming bound controls the number of small free
   components. A component larger than K uses at least K+1 values,
   giving the literal |S|/(K+1) budget for all large components.
4. The full actual value kernel embeds in the graph solution space.
   No residual-rank estimate is a premise of the proof.

`PrimeFactorBudget` proves 2^omega(n)<=n and the logarithmic prime-factor
bound. Polynomial-height coefficients therefore add a negligible number
of omitted rows. The small-prime budget is discharged by the already
proved elementary prime-count bound; no literature estimate is assumed.

## Uniform normalized-pair result

The critical-band threshold is chosen before all source positions and
all positive a<=b<=(L+1)^3. One actual equality

    b*label_x(i) = a*label_y(j)

puts the deduplicated normalized union in an interval of width 2bL,
with base at least N/2 for all sufficiently large N. Its cardinality is
at most 2B, where B=L+1. Thus `NormalizedPairResidual.rank_sublinear`
proves its actual full value kernel is uniformly o(B).

`NormalizedPairRankLoss.loss_le_units_add_residual` bounds the full
pair deficiency 2L-rank(S_x+S_y) by (u-1)+rank(valueKernel U), where
u is the actual number of exact units. This deficiency includes internal
local rank defects and dominates the actual intersection rank. For
coprime a,b, the exact unit count then gives, uniformly,

    pairLoss <= (u-1)+epsilon*B,
    pairLoss <= L/b+epsilon*B.

These are `AlignedPairRank.units_residual_bound`, `channel_bound` and
`actual_intersection_bound`. The common threshold depends on the fixed
critical-band width and positive epsilon. Separation, affine compatibility
and local regularity are unnecessary. One exact unit suffices. These
weakened hypotheses and explicit finite bounds are P1-MATH-0039.

## Remaining scope

The final O(B/log B) assertion of T1.9 for fixed channel height and a
fixed enlarged prime cutoff is separate unfinished work. For T1.11
and T2.6, the generic residual arithmetic on true subsets of two
progressions is now available, but the actual target/old quotient-rank
bridge, endpoint exceptions and old-information extension are not yet
closed. All three numbered statements remain in progress. No new Paper C
port, external mathematical assumption, manuscript revision or Palomar
registration is introduced.
