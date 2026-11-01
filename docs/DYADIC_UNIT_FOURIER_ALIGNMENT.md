# Actual dyadic unit Fourier aggregate and its signed main term

This extends P1-MATH-0044 and prepares article 3.3 and companion T2.5.
The complete unit-word, pattern and dyadic-source aggregation bridge is
proved. Exceptional-normalization removal and the full mass/profile
asymptotics remain unfinished. No numbered result is newly counted complete.

## Pair-specific shapes and global patterns

The [local word bijection](SELECTED_UNIT_WORDS_ALIGNMENT.md) expresses
the actual signed nonzero even-unit sum for each fixed pair as the sum
of A_d times both predecessor placement signs over its fitting shapes.

`UnitShapePatterns.patternEquiv` identifies these shapes with the global
patterns whose two initial placement indices form an actual exact unit
of that pair. Both maps are explicit and inverse. A genuine placement
index is proved unchanged by the finite-index conversion; no modular
identification merges distinct placements.

Thus the fixed-pair unit sum equals the literal integer pattern sum
whose term is zero when that pattern's initial unit is absent.
`DyadicUnitFourierAggregate.pair_pattern_sum` transports this equality
to the actual real-valued signed unit sum.

## Actual dyadic host reindexing

`DyadicUnitWordHosts.weighted_unit_hosts` sums one pattern's exact unit
indicator over the two actual dyadic centres. Its value is the literal
source-pair cardinality times that pattern's coefficient. The finite
filter is proved equal to `DyadicEndpointPairs.sourcePairs`.

Finite sum interchange then gives `integer_dyadic_sum`. Its real
transport, `dyadic_unit_sum`, proves

    sum_(x,y in dyadicBlock N) signedUnitSum(a,b,x,y,L)
      = forwardHosts(N,L,a,b).

For N>(a+b)(L+1) and positive a<b, the actual two orientation source
families are disjoint. Their cardinality is twice the forward cardinality.
`signed_hosts_twice_forward` and `symmetric_unit_sum` therefore prove

    2 * sum_(x,y in dyadicBlock N) signedUnitSum(a,b,x,y,L)
      = signedHosts(N,L,a,b).

This counts the actual source units at every pattern. Multiple patterns
on one pair are retained as distinct actual Fourier words, as required
by the preceding local bijection. No unweighted union replaces this sum.

## Exact error and height uniformity

For N>=2, positive coprime a<b<2a, B=L+1 and N>(a+b)B,
`finite_signed_sum_error` combines the exact preceding identity with
the already proved literal translation estimate:

    |2*sum signedUnitSum - N*w(a,b)*S_{a,b}(L)| <= 6B*U_{a,b}(L).

The main term retains its sign. Its error alone uses the positive sum U.
The coefficient is exactly w(a,b)=2*(2a-b)/(a*b), with the finite
Euclidean remainder, empty-word cases and contact terms all retained.

`DyadicUnitFourierCount.all_heights` supplies one threshold in the
critical band, before all reduced positive a<b<2a with b<=B^3.
It derives N>(a+b)B from the uniform polynomial/logarithmic scale bound.
There is no fixed-height assumption hidden after the threshold.

## Actual probability scope and remaining work

The summed expression is the actual rational-unit Fourier contribution.
On each private normalized pair with positive length, the earlier
[actual covariance formula](PRIVATE_UNIT_COVARIANCE_ALIGNMENT.md)
identifies p^2 times this sum with q_{x,y}-p^2. Probability-zero pairs
retain their character cancellations. On a nonprivate pair, the rational
unit sum has no asserted equality with the complete covariance.

To obtain the source's fixed-channel mass, defective normalized hosts
must still be removed and the p^2 baseline added on the retained private
dependent family. Their errors and the full mass/profile asymptotics
and positive phase equivalents remain unfinished. Neither article 3.3
nor companion T2.5 is declared proved.

No new literature premise, Paper C port, manuscript revision or Palomar
registration is introduced. Original manuscript bytes are unchanged.

Validated actual dyadic unit-Fourier checkpoint (9,369 build jobs;
3,506 audited declarations; 1,221 directly checked coverage/finding names):
[74727a964e38c4b8b556fac2f93194485c695c11](https://github.com/Vulkin-prog/paper-p1-lean/commit/74727a964e38c4b8b556fac2f93194485c695c11).
