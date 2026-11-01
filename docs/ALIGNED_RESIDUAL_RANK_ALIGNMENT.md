# Companion T1.9 — full enlarged geometric alignment

Source: companion T1.9, page 14, `p1:arith:alignedrank`,
`companion_sections/arithmetic_appendix.tex:770`, statement hash
`7de9608ecc780ef5a448579b04b2ebeabe5e1157579ce3025b0303a047157acc`.
The full statement is proved, including zero exact units and both
coefficient orientations. Original source bytes are unchanged. The
[scope audit](FORMALIZATION_SCOPE_AUDIT.md) retains the initial one-unit
coverage mistake and its subsequent closure.

## Literal geometric hypothesis

`EnlargedPairGeometry.Geometric a b x y L` means exactly

    |b*x-a*y| <= (a+b)*B,   B=L+1.

For positive a<=b, the actual deduplicated union U=bV_x union aV_y
lies in [b*x-3*b*B,b*x+3*b*B]. Its cardinality is at most 2B. With
b<=B^3, the radius is at most 3B^4. At a uniform critical-band threshold,
the interval base is at least N/2 and is at least twice its width.
Its logarithm is bounded below by a positive multiple of B, and the
logarithm of 64 times the width is at most 13 log B. These bounds use
only the literal geometric inequality, including when u=0.

## Actual residual, Runge, coding and prime rows

`FiniteResidualRank.valueKernel U` is the full prime-parity kernel on
the actual distinct normalized integers. Omit exactly primes <=B and
prime factors of ab. Every remaining prime row meets at most two
vertices. Its graph and pins come from the actual row supports.

For a true subset S of two dilated intervals, r omitted primes,
component cutoff K and coding radius t>=1, the finite estimate is

    rank(valueKernel S)
      < max(r+1, 2t*2^((r+1)/t+1)) + |S|/(K+1),

provided S lies in [U,U+R], R>=1, 2R<=U and (64R)^(2Kt)<U.
The displayed quotients are natural-number quotients. Component value
sets are nonempty and disjoint. The appended parity row is component
size modulo two. A nonzero kernel word selects an actual nonempty even
square product. The proved degree-uniform Runge bound excludes short
words; the finite Hamming estimate bounds small components, while a
large component uses at least K+1 vertices. The literal prime budget is
O(B/log B), proved from the elementary prime-count and factor bounds.
Choosing K before the threshold gives the uniform residual o(B).

`EnlargedAlignedResidual.row_rank_sublinear` controls the whole actual
remaining-row solution space. `full_rank_sublinear` bounds its full
value-kernel subspace. Neither result assumes an exact unit.

## Zero units and actual pair deficiency

`NormalizedPairRankLoss.pairLoss x y L` is 2L-rank(S_x+S_y), including
internal local deficiencies. It dominates the actual intersection rank.
When u>0, an actual common value gives the usual common-anchor argument.
When u=0, the full span of the normalized union has dimension at most
two plus the sum of its two even spaces. The rank-nullity identity on
the literal union then proves pairLoss<=rank(valueKernel U).

The all-case finite lemma `loss_le_units_add_residual_all` therefore gives

    pairLoss <= (u-1)_+ + rank(valueKernel U).

The exact channel count also covers u=0. Applying it in the orientation
with the larger coefficient second, then swapping back, yields

    pairLoss <= (u-1)_+ + epsilon*B,
    pairLoss <= L/max(a,b) + epsilon*B,
    actualIntersectionRank <= L/max(a,b) + epsilon*B.

`EnlargedAlignedPairTheorem.uniform_bounds` chooses a common threshold
before every positive coprime pair a,b with max(a,b)<=B^3 and every
actual source pair. Separation, compatibility and local regularity are
unnecessary. This stronger conclusion extends P1-MATH-0039.

## Fixed height and enlarged prime cutoff

`IntervalResidualKernel.largeKernel S H` imposes exactly all prime-parity
constraints above H. If S lies in [U,U+R] with R<=H, every nondefective
value has a private prime above H, so its kernel coefficient is zero.
Restriction to the actual defective values is injective and the rank is
at most card(defectsInInterval H U R).

At fixed height bound Q, the enlarged-alignment interval has width
6*max(a,b)*B<=6QB, with N/2<=U<=2QN eventually. For every fixed D>=0,
`EnlargedAlignedPairTheorem.fixed_height_residual` chooses K>0 before
the critical-band width C, then one threshold before all source pairs
and all cutoffs satisfying

    6*max(a,b)*B <= H <= D*B.

The actual large-prime kernel is <=K*B/log B. In particular H=6QB is
admissible. The full kernel embeds in it, giving the full-kernel rate
and `fixed_height_loss` with (u-1)_++K*B/log B. Both orientations and
zero units are included. `companion_T1_9` packages the full uniform and
fixed-height assertions as literal quantified statements on actual maps.

## Preserved narrower proofs and remaining work

The earlier `AlignedPairTheorem.one_unit_T1_9` remains valid with its
explicit one-unit premise and its smaller cutoff 2bL. Its uniform
checkpoint is df34686b343f5297c181e6150e21834acc335ad8; its fixed-height
checkpoint is 6165382c14d6f8e653ddec27accb9c042628ae10. These checkpoints
alone did not cover the full enlarged-alignment source statement.

T1.11 and T2.6 remain in progress. Their [bounded-affine dyadic core](DYADIC_MATCHING_ALIGNMENT.md)
and [finite target quotient-rank bridge](TARGET_QUOTIENT_RANK_ALIGNMENT.md)
are proved. The actual combined target-union asymptotic and construction
of bounded affine data from literal geometric alignment remain open.
No new Paper C port, external mathematical assumption, manuscript revision
or Palomar registration is introduced.

Validated full enlarged-alignment T1.9 (9,295 build jobs; 3,319 audited
declarations; 1,034 directly checked coverage/finding names):
[e4d183ed6e300f0352f6164c1c049cadfe0c0db4](https://github.com/Vulkin-prog/paper-p1-lean/commit/e4d183ed6e300f0352f6164c1c049cadfe0c0db4).
