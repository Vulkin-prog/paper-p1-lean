# The integer product tail — companion T20.2

**Status: proved.** Source: companion V1.6, page 82,
`companion_sections/offset_geometry.tex:70`, label
`p1:offset:integer-tail`. Exact statement SHA-256:
`d152e541850e3b572b1faf9f52c652ec80cb933639af0d559be599a9c0cec5cc`.

## The literal product sum

`IntegerProductTail.productTail s T` is the ordinary countable sum over
pairs of positive integers with product exceeding T. Natural indices a,b
encode those integers as a+1,b+1. `pairTerm_eq_power` identifies the summand
with the literal product to the power -s, restricted by the strict cutoff.
`summable_pairTerm` proves absolute convergence for every s>1 by domination
with the product of two convergent positive p-series. `productTail_eq_rows`
then justifies the iterated sum; it does not assume a rearrangement of a
potentially divergent series.

## Real thresholds and the two ranges

`PowerSeriesTail.tail_eq_shifted` handles every real nonnegative cutoff
using its exact natural floor. The integral test starts at that floor,
which is at least T/2 for T≥1. Evaluation of the improper integral gives

`sum_(n>T) n^(-s) ≤ C_s T^(1-s)`,
where `C_s=2^(s-1)/(s-1)>0`.

For a≤T, apply this inequality at T/a and multiply by a^(-s). Exact
real-power identities reduce the result to `C_s T^(1-s)/a`.
The harmonic-number bound gives the sum over these a. For a>T, dominate
the inner sum by the full positive p-series Z_s and apply the tail bound
to the remaining outer sum. This proves the finite-cutoff estimate

`productTail(s,T) ≤ C_s T^(1-s)(1+Z_s+log T)`.

No limiting argument discards an endpoint or integer floor.

## The source's quantifiers

`productConstant s` is the explicit positive number
`C_s*((1+Z_s)/log 2+1)`. `companion_T20_2` chooses this number once for
each fixed s>1 and proves, simultaneously for every real T≥1,

`productTail(s,T) ≤ productConstant(s) T^(1-s) log(2T)`.

There is no growing exponent, arithmetic window, model regularity or
unstated dependence on T in the constant.

## Inputs and validation

The only library inputs are proved at Mathlib commit
`9d581dfff2e41de989072ea63abf3daf69311520`:
`Real.summable_nat_rpow`, `AntitoneOn.tsum_comp_add_le_integral`,
`integrableOn_Ioi_rpow_of_lt`, `integral_Ioi_rpow_of_lt`,
`harmonic_floor_le_one_add_log`, and standard absolutely summable-series
and real-power identities. No target tail bound or literature estimate
is a theorem premise. No additional Paper C proof is ported.

The full Lean v4.36.0-rc2 build passed (8,753 jobs), followed by the actual
axiom audit of all 1,775 project theorem/lemma declarations. Only `propext`,
`Classical.choice` and `Quot.sound` occur. Coverage is 23 / 167 numbered
results: 9 main and 14 companion. No new mathematical correction or
improvement is identified, and no Palomar registration is made.
