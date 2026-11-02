# Arbitrary translated rational windows: absolute finite endpoint error three

A finite divisibility proof makes the canonical-overlap endpoint
error explicit and covers arbitrary independent translations of the
three windows. For primitive u<v<w<2u, every L>=0 and every actual
center vector X with X_i>=2, let U be the union of the three complete
windows normalized by (v*w,u*w,u*v). The checked bound is

3L-(U.card-1) <= D(u,v,w)*L+3.

No geometric alignment, common normalized value, dyadic restriction,
private prime, even-rank injectivity or affine compatibility is needed
for this finite cardinality statement. It implies
U.card-1 >= (71/30)*L-3, and at least (43/18)*L-3 away from
(10,12,15). The absolute error 3 is uniform in all slope heights and
translations. The previous explicit zero-intercept specialization had
error 5; the manuscript itself stated an unspecified absolute O(1).

The proof counts the third window only once. All its coincidences
with the first two windows lie in the union of divisibility classes
w/gcd(u,w) and w/gcd(v,w). Their least common multiple is exactly w
by primitive normalization. Exact floor counts in an arbitrary
complete positive-integer window give upper errors 1,1 and a lower
error 1 for their intersection. Combining this union bound with the
first-pair count proves the finite loss bound, without requiring a
lower bound on the actual triple intersection. In particular, the
three pair-overlap locations need not coincide.

If the normalized intersection graph is connected and the union has
full even rank, this finite result yields actual affine joint
probability bounds with constants 2^(3+(71/30)*C) and
2^(3+(43/18)*C), retaining the original infinite prime-sign law and
all zero-probability incompatible systems. Predecessor exclusivity
is not required for these upper bounds. The asymptotic exponents and
the unique extremal physical triple are unchanged.

P1-MATH-0099 records the new explicit finite proof and bound.
P1-MATH-0067 gains this arbitrary-translation actual-probability
application. Main 14.2 remains proved; main 14.3 remains in progress:
the full affine host aggregation, deficient normalized kernels at
growing height and nonaligned targets are still open. The total
third-cumulant lower passage is unchanged. Coverage remains 79/167;
confirmed improvements rise to 99. No original source, dependency,
external estimate or Palomar state changes.

Verified with Lean v4.36.0-rc2: full lake build (11185 jobs), actual kernel-axiom audit (7434 declarations; only propext, Classical.choice and Quot.sound), 5151 ledger/finding declaration checks, all 138 source manifest entries and 167 numbered-result hashes preserved; 14.75 GiB free on Ubuntu root.
