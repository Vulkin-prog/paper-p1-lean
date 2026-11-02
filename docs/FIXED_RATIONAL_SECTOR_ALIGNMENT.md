# All fixed-height rational triples: residual defect and sharp mass

All zero-intercept rational triples at fixed bounded slope height
now satisfy the sharp actual probability and mass upper exponents,
without a private-prime condition, even-map injectivity, local regularity
or an assumed affine compatibility witness. Incompatible systems are
included through their actual zero probabilities.

Fix Q>=1 before N. For primitive 0<u<v<w<2u with w<=Q, t>=1 and
u*t in the dyadic block, the entire merged product-normalized union
lies in one interval of width 2*Q^2*B, at a base between N/2 and
2*Q^2*N for large critical N. Its full value kernel embeds in the
large-prime kernel, which is supported on actual defective values of
that interval. The already proved local defect count gives a uniform
O_Q(B/log B) bound and hence an arbitrarily small multiple of B.
No Pila or BCN estimate is invoked.

A general finite family inequality retains the whole full-value defect:
union.card-1 <= actual joint rank + full normalized value-kernel rank.
It needs a common normalized value or connected normalized overlap,
with no independence assumption. The actual affine joint mass is at
most the inverse binary power of its actual joint rank, including zero
mass. Combining these checked facts with the rational union-cardinality
bounds proves actual point bounds N^(-71/30+epsilon), and
N^(-43/18+epsilon) away from (10,12,15), uniformly over all w<=Q.

The literal population contains every primitive dyadic zero-intercept
triple of height at most Q, including defective normalizations and
irregular windows. Its ordered count is at most 16*(Q+1)^3*N.
Summing actual probabilities gives ordered and unordered mass bounds
N^(-41/30+epsilon), and N^(-25/18+epsilon) in the nonextremal sector.
Q is fixed before the threshold; these unconditional bounds do not
assert uniformity for Q growing as a power of B.

The extremal private witnesses normalize by (6,5,4), whereas the
product normalizers at (10,12,15) are 30*(6,5,4). The checked common
dilation invariance transfers their full even rank exactly. Their
actual joint-probability sum is at least
(2^(-4-(71/30)*C)/120)*N^(-41/30). It embeds in the even-rank
polynomial-height population and, for Q>=15, in the unconditional
fixed-height population. Both sectors therefore attain the sharp
41/30 exponent. In the even-rank sector, the actual nonextremal mass
is at most an explicit constant times N^(-1/45+epsilon) times the
full mass; it is uniformly negligible in the critical band.

This extends P1-MATH-0067 and P1-MATH-0098 without a new improvement
identifier. The full aligned-family proposition 14.3 remains open:
arbitrary affine intercepts, growing third-slope height, nonaligned
targets and all source contact configurations are not covered here.
Main 14.5 retains its positive connected lower bound but not the total
third-cumulant passage. Coverage stays 79/167 and findings stay 98.
The original sources, dependencies and Palomar state are unchanged.

Verified with Lean v4.36.0-rc2: full lake build (11177 jobs), actual kernel-axiom audit (7416 declarations; only propext, Classical.choice and Quot.sound), 5133 ledger/finding declaration checks, all 138 source manifest entries and 167 numbered-result hashes preserved; 14.77 GiB free on Ubuntu root.


## Arbitrary affine positions and explicit canonical endpoint error

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
