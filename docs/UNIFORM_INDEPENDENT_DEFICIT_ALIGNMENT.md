# All-cardinality independent deficit: uniform Euler-average foundations

Source: `main_sections/exact_transfer.tex:323`. The final independent deficit remains open.

Preparation of the all-cardinality independent deficit15.6:
the rough-prime WINDOW AVERAGE in its proof is now established
unconditionally, with an explicit constant and without treating
the number of exposed sources as fixed. Main15.6 moves from
not_started to in_progress. Its final deficit estimate is NOT
yet proved. Coverage remains84/167 proved and16 conditional,
with128 confirmed mathematical improvements. This checkpoint
adds arithmetic foundations and no new numbered completion.

FiniteEulerAverage proves the exact finite divisor expansion
of an arbitrary nonnegative local Euler product over a finite
set of distinct primes. For every natural X, the average over
1<=n<=X is at most
X*product_p(1+h(p)/p).
The exact expansion uses the actual count floor(X/d) of positive
multiples of the product d of the selected distinct primes.
Primality supplies the actual coprimality implication d|n iff
every selected prime divides n. In particular there is no
spurious +1 term for each modulus in this first-moment bound.

InverseSqrtTail proves the finite elementary bound
sum_{Y<n<=X} n^(-3/2) <= 2/sqrt(Y), for every Y>=1.
It telescopes reciprocal square roots and does not invoke an
analytic tail premise or any prime-distribution estimate.
RoughEulerMoments uses the cutoff Y=64*B^2 and the actual
factor p^(-1/2). For p>Y the moment increment
h_B(p)=(1+p^(-1/2))^B-1 is at most8*B*p^(-1/2).
The already proved elementary exponential remainder gives
this bound since B/sqrt(p)<1/8. The finite tail bound gives
sum_p h_B(p)/p<=2 for EVERY finite prime set above this cutoff.
Consequently the actual B-th moment of the local rough-prime
Euler product, summed over1<=n<=X, is at most X*exp(2),
uniformly in B and in the actual finite prime set.

FiniteProductPowerMean proves the pointwise AM-GM inequality
product_i f_i <= average_i f_i^B for B positive positions,
and the finite first-moment consequence after interchanging
the actual sums. This suffices in place of the printed Holder
step. WindowEulerAverage.first_moment applies it to every true
position x-1+i of an actual complete dyadic window. Each fixed
position maps the actual starts injectively into1..3N.
For N>=2 and1<=B<=N+1 it proves
sum_{N<=x<2N} product_{i<B} product_{p in P,p|(x-1+i)}
  (1+p^(-1/2)) <= 3*N*exp(2),
for EVERY finite prime set P above64*B^2. This product counts
a prime once for every position it divides and therefore also
majorizes the single-occurrence union-of-primes product in
the manuscript. The explicit bound is independent of B.

The constant enlargement from the printed cutoff B^2 to64*B^2
is internal to these new lemmas; no preserved manuscript is
changed. The old-source Euler factor, the actual relative
exceptional exposure count and its entire cardinality sum
remain to be connected before15.6 can be completed. No desired
deficit bound or growing-order arithmetic constant is assumed.
There is no new geometric or literature input, PaperC port,
dependency download, original-source edit or Palomar registration.

The JSON result row records full validation and its exact proof commit.


## Complete arithmetic row budget

The ARITHMETIC exposure budget for article15.6 is now proved
unconditionally with a threshold before every number of preceding
windows. Its final independent deficit sum is still OPEN.
Main15.6 remains in_progress; coverage remains84/167 proved,
16 conditional and128 confirmed mathematical improvements.

LogBudgetEuler proves the finite prime Euler-product estimate
exp(c*sqrt(Y)/log(Y)+K/(sqrt(Y)*log(Y))) from the ACTUAL prime
logarithmic budget sum(log(p))<=K. Small primes are bounded by
the proved elementary weighted-prime estimate; above Y each
inverse square root is charged to log(p)/(sqrt(Y)*log(Y)).
No prime-pool cardinality estimate is substituted for its log
budget. EulerPrimeCovers proves the monotonicity and finite
union-cover bounds, allowing repeated prime occurrences and
arbitrary overlaps.

IndependentExposurePrimePool defines the literal old-source
pool together with ALL primes up to Y=64*(L+1)^2. Its Euler
factor baseEuler(S,L) is at most N^epsilon uniformly for every
actual dyadic source set S with card(S)<=s, where s is fixed
before N. The actual log budget is
Y*log(4)+B*log(4)+s*B*log(3N), B=L+1.
Since sqrt(Y)=8B, the exponent is at most
[8*(c+log(4))*B+log(4)/8+s*log(3N)/8]/log(Y).
Critical-window geometry puts B<=D*log(N), and a fixed minimum
length makes log(Y) arbitrarily large before any actual source
is supplied. Thus this factor is uniformly subpower. All primes
of the real source values are retained.

IndependentExposureEulerBudget defines the actual rough-prime
window product A_x, with primes bounded by3N and above Y.
It has A_x>=1 and the already proved first moment at most
3*N*exp(2). For any fixed old source set S and ANY new set A
of dyadic windows, with NO bound on card(A), it proves
Euler(primePool(rawValues(S union A)))
  <= baseEuler(S,L)*product_{x in A} A_x.
The literal prime-set cover follows from actual prime factors
of actual true window values. A prime at most Y goes into the
base pool; every larger prime from a new window occurs in its
actual positionwise rough-prime Euler product.

For arbitrary weights w_x<=M/N, M>=0, the same development
proves sum_x w_x*A_x<=3*M*exp(2). The exact exceptional row is
BranchingExceptional.badStarts for all raw old source values.
Its weighted mass is at most
rowConstant(S,N,L,M)*product_{x in A} A_x,
where rowConstant=(M/N)*(B/2)*sqrt(3N)*baseEuler(S,L).
This uses the exact supported-value Euler count, including
contacts and local defects, with no separate contact deletion
or worst-case arithmetic constant depending on card(A).

UniformIndependentExposureBudget.uniform_row_constant proves
rowConstant<=N^(-1/2+epsilon), uniformly in fixed-cardinality
sources. uniform_budget therefore supplies ONE threshold
before all N,L,S,weights and arbitrarily large preceding sets A,
simultaneously with the constant weighted mean of A_x. These
are actual arithmetic row estimates, not assumptions of the
desired final independent deficit.

The remaining work for15.6 is finite: relate failure of the
literal source-plus-target directness to an exceptional exposure
in every ordering, retain the exact factorial enumeration, and
sum the weighted exposure bounds over all cardinalities. This
checkpoint asserts none of these unfinished closure steps.
No new external input, dependency download, PaperC port,
manuscript-byte change or Palomar registration is added.

The JSON row records this checkpoint validation and exact proof commit.


## Unconditional completion at every cardinality

Main Lemma15.6 is now proved UNCONDITIONALLY for the literal
independent deficit summed over ALL cardinalities. One threshold
is chosen before N,L,all actual dyadic source and target sets,
every source set of cardinality at most the fixed s, and every
subspace W of the FULL RAW source value span. The result is
therefore stronger than restricting W to the effective source
span. The ground set G may be any actual subset of the dyadic
block; targets are exactly G minus the sources.

IndependentExtensionDeficit.Direct means literal injectivity of
the addition map from W and the individual effective spaces S_x.
Its equivalence with zero relative nullity is proved. The finite
population is exactly every target subset for which this map
is not injective, with no restriction on cardinality. Its weight
is exactly u^card(U)*product_{x in U} infiniteMarginal(x,L),
proved equal to product_{x in U}(u*infiniteMarginal(x,L)). Zero
marginals are retained. These are independent product weights,
not conditional extension probabilities or positive joint weights.

IntersectionExceptional proves that a nonzero vector belonging
both to an actual effective window space and to the full old
raw-value span forces at least two supported physical positions.
The even coefficient vector is lifted from the actual effective
space; its nonempty binary support has even cardinality. Every
selected coordinate lies in the real old prime pool by the
already proved private-prime argument. Thus its center belongs
to the literal BranchingExceptional.badStarts set. The effective
source span is proved to lie in the raw source-value span. The
latter has an actual finite enumeration from the full coefficient
map, so arbitrary source subspaces can be used without assuming
local regularity or a dimension formula for W.

For each non-direct U, choose a minimal relative dependent J
inside U. A genuine relation is nonzero in every target of J;
its sum lies in W. Choose x in J and put A=J minus x. The x
component is nonzero and lies in the full raw span of sources
union A. Hence x is an actual exceptional start relative to A,
and insert(x,A) is a subset of U. This covers internal target
dependence as well as dependence meeting W. The W component
may vanish, and no nonzero-source-component condition is added.

AllCardinalitySeedBound proves the exact finite identity for
all supersets of a seed D inside G:
  sum_{D subset U subset G} product_U w
    = product_D w * product_{G minus D}(1+w).
ExceptionalSeedBound then bounds every covered family by
  exp(sum_G w) * sum_{A subset G} product_A w * badRow(A).
If badRow(A)<=D*product_A a, a_x>=1, and
sum_G w_x*a_x<=K, this is at most D*exp(2K).
This is a pure finite unordered argument; no enumeration by
orders, factorial normalization or growing-order constants
are used in this closure. Overcounting is justified solely by
nonnegative finite sums, including overlaps between witnesses.

UniformIndependentDeficit.finite_bound applies this identity
to the actual source-relative seeds. The published arithmetic
row budget supplies D=N^(-1/2+eta), a_x=windowEuler(N,L,x),
and K=3*M*exp(2), where M=u*2*2^C is a uniform actual marginal
cap. These inputs hold before arbitrarily large preceding sets A.
The already proved first moment bounds K independently of N,L.
With eta=epsilon/2, the fixed factor exp(2K) is absorbed using
a second epsilon/2. UniformIndependentDeficit.uniform_bound
therefore proves the full printed N^(-1/2+epsilon) estimate,
uniformly in sources and W, at every cardinality simultaneously.
Contacts and local defects remain in the exceptional row; no
extra contact deletion or correction term is necessary.

Main15.6 moves from in_progress to proved. Numbered unconditional
coverage rises from84 to85/167;16 conditional results remain
separate. P1-MATH-0129 records the unordered finite closure and
the stronger raw-source-space scope. This result does not prove
the compressed clause of15.8 or the pair-weighted total15.9.
No new geometric input, dependency download, PaperC port,
manuscript-byte change or Palomar registration is introduced.

The JSON row and finding129 record complete validation and the exact proof commit.
