# Weighted canonical-pattern translation aggregates

This extends the [actual translation checkpoint](SOURCE_TRANSLATIONS_ALIGNMENT.md)
and [finite channel calculation](FINITE_CHANNEL_SUMS_ALIGNMENT.md).
It is preparatory to article 3.3 and companion T2.5; neither numbered
probability/mass statement is counted complete.

## Exact finite pattern family

`ChannelWordHosts.Patterns L a b` is the dependent finite family of

- positive gaps d in 1,...,floor(L/b);
- a true first-block placement in `placements L (a*d)`;
- a true second-block placement in `placements L (b*d)`.

A pattern has positive weight A_d, already proved to be the actual
endpoint-selected binary even-selection cardinality. Its sign is the
product of the two literal predecessor-placement signs. Thus every
interior selection with those extremes has the prescribed same sign.
`placement_index_val` proves that each actual placement is its unchanged
source index; the total index function does not wrap a genuine placement.

`pattern_sum` proves equivalence of the dependent-type sum and the
literal nested finite sums. The positive and signed total weights are
proved to be exactly U_{a,b}(L) and S_{a,b}(L), respectively.
In particular U>=0 and |S|<=U. Empty sums are included.

## Actual source-pair counts at each pattern

`sourceCount N p` is the actual two-orientation dyadic source-pair
cardinality at that pattern's two first-unit positions. The finite
interval/source-pair bijection was proved at the preceding checkpoint.
The pattern aggregate weights this literal count by A_d, with or without
the literal predecessor sign. Sources can appear at several distinct
patterns, as intended by the weighted canonical count.

For N>(a+b)B, positive coprime a<b<2a and B=L+1, the existing count
error is <=6B at every pattern. `WeightedTranslationError.weighted_error`
proves the finite summation inequality for nonnegative weights and signs
of absolute value at most one. Applying it yields

    |unsignedHosts-N*w(a,b)*U_{a,b}(L)| <= 6B*U_{a,b}(L),
    |signedHosts-N*w(a,b)*S_{a,b}(L)|   <= 6B*U_{a,b}(L).

The signed main term is retained. Replacing it by an unsigned total
would lose the predecessor cancellations. Absolute values are used only
in bounding the error.

## Uniform critical-band threshold

`ChannelWordHostCount.all_heights` gives one common threshold before
every reduced channel a<b<2a with b<=B^3 and all finite patterns.
The coefficient w=2*(2a-b)/(a*b) is the actual two-orientation dyadic
coefficient, with w(2,3)=w(3,4)=1/3.

This extends P1-MATH-0044; it is not a new independent finding count.
The finite source-family counts and their signs are proved, not assumed.
No bound on the target probability/mass is an input to these theorems.

## Remaining identification and exceptional sources

The canonical-pattern aggregate must still be identified with the
actual complete unit-relation/Fourier contribution on private normalized
value sets. This requires the relation-kernel and word-enumeration bridge;
no equality with the actual probability is asserted here.
Defective-normalization removal, full fixed-channel mass, complete pair
profile and asymptotic phases also remain open. Original manuscript
bytes are preserved. No external mathematical hypothesis, new Paper C
port, manuscript revision or Palomar registration is introduced.

Validated weighted canonical-pattern checkpoint (9,329 build jobs;
3,409 audited declarations; 1,124 directly checked coverage/finding names):
[88ce8a72b7b579b3b7442de98efd91af4b445764](https://github.com/Vulkin-prog/paper-p1-lean/commit/88ce8a72b7b579b3b7442de98efd91af4b445764).

The subsequent [exact unit-intersection checkpoint](EXACT_UNIT_INTERSECTION_ALIGNMENT.md)
constructs the actual even-unit/common-class linear equivalence, including
zero and one unit. Affine character signs, selected-word enumeration and
the actual Fourier/probability identification remain open.
