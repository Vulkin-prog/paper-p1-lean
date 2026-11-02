# CompanionT17.4: actual finite analytic conversion

Source: `p1:close:conversion`, `companion_sections/closure.tex:323`, page64. Status: **in progress** for the arithmetic covariance scale. Original source bytes are preserved.

The full analytic finite conversion is now proved for actual atomic
signed measures. Finite signed laws carry their ordinary l1 ring norm;
its nondegeneracy and exact scalar behavior are proved. Their completion
is a real Banach algebra. Singleton evaluation extends continuously,
and every completed element has an absolutely summable coefficient
sequence whose ordinary l1 sum is bounded by its completion norm.
Consequently all norm estimates below control genuine actual signed
measures, including their infinite tails.

The convolution exponential exp(mu*Delta) is proved coefficientwise
equal to the actual Poisson mass exp(-mu)*mu^k/k!. Its positivity and
probability interpretation are proved for mu>=0. Convolution byDelta
is actual translation minus the identity; convolution byDelta^2 gives
the literal second difference. The completed quadratic reference is
proved equal to the existing actual signed-measure Q(mu,alpha).

For every elementv of a real Banach algebra, absolute exponential
series prove a Taylor tail at every order, with no small-norm premise.
Finite-product perturbation and actual quadratic cancellation give

    ||(1+v)^n-exp(v)^n+(n/2)*v^2*exp(v)^n||
      <= (2n||v||^3+n^2||v||^4)*exp((n+2)||v||).

No convolution logarithm is used. For every integern>=2,0<=p<=1,
np<=A and arbitrary realbeta,c2, write mu=np and alpha=2c2-np^2.
The actual finite reference b^n+beta*Delta^2*b^(n-2) satisfies

    ||reference-Q(mu,alpha)||_1
      <=4|beta-c2|
        +16exp(2A+4)*(np^3+(np^2)^2)
        +16exp(2A+2)*|c2|*(p+np^2).

Both finite binomial expansions in the source proof, the deletion of
two Bernoulli factors, the exact quadratic coefficient and the
beta-replacement cost are proved. The source restriction2p<1 is
unnecessary for this analytic step; the valid finite scope is0<=p<=1.

The critical mean and p<=2^C/N are proved inputs, not assumptions.
An explicit positive errorConstant(C), chosen before everyN,L,n,beta,
c2, yields

    ||reference-Q||_1
      <=4|beta-c2|+K_C*(N^(-2)+|c2|/N)

for everyN>=2,2<=n<=N and critical-bandL. The actual regular-set
cardinality is proved eventually at least2 under one uniform
threshold. Thus the same estimate holds for the literal actual
RetainedReferenceTheorem.binomialReference, with its actual good-edge
joint-moment sum beta. All measures and the ordinary sum of absolute
singleton differences are included.

The arithmetic bound C_2=O(a_N) used in the source is not yet proved.
No such bound is assumed or counted as completion: T17.4 is in progress,
with exactly this remaining obligation. Proved coverage remains77/167
(main28/73, companion49/94). P1-MATH-0084 records the logarithm-free
finite extension; confirmed findings84. No external mathematical input,
BCN argument, Paper C port, dependency download, manuscript-byte change
or Palomar registration is added.

## Validation

Lean v4.36.0-rc2 full build passed (10619 jobs); actual axiom audit passed for all 6130 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 3847 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 15.83 GiB. Actual finite-law l1 completion, summable singleton coefficients, exact Poisson exponential and quadratic signed-measure identification, unrestricted Banach exponential Taylor bounds, finite-product perturbation and explicit finite Poisson–Charlier conversion are proved. The actual regular-set reference has uniform error4|beta-c2|+K_C*(N^(-2)+|c2|/N), with no2p<1 premise. The arithmetic covariance scale C_2=O(a_N) remains open; T17.4 is in progress and adds no proved coverage. Coverage77/167 (main28/73, companion49/94); confirmed findings84. No external mathematical input, BCN premise, Paper C port, dependency download, manuscript-byte change or Palomar registration.

Validated proof checkpoint: [968fa9b38502cef818cb8ed04babda3a6c3843ea](https://github.com/Vulkin-prog/paper-p1-lean/commit/968fa9b38502cef818cb8ed04babda3a6c3843ea).


## Universal-constant strengthening

A further strengthening of the finite analytic conversion is proved:
the constant is universal, C=16exp(2), with no upper bound on the total
mean. For arbitrary finite Bernoulli marginals0<=p_i<=1, arbitrary
signed weights on selected two-element subsets, and any nonnegative
upper marginal capP,

    ||B_2-Q(mu,2C_2-s_2)||_1
      <=16exp(2)*(s_3+s_2^2+A_2*(s_2+P)).

No mean bound mu<=M or small-marginal condition is required. The actual
Bernoulli convolution factors and actual Poisson factors are proved to
have normone. Their finite products are contractions. Exact insertion
identities and absolute exponential tails then need only the local
increment cap ||p_i*Delta||<=2, rather than a bound involving their sum.
Every contraction premise of the generic algebra lemma is discharged
for the actual probability factors; the target conversion is not an
input. All actual signed singleton masses and infinite tails remain
controlled by the ordinary l1 norm.

The universal inequality is instantiated on actual original-run
Bochner marginals and centered pair coefficients, with the actual count
mean and exact variance-minus-mean parameter. The full diagonal term
and all covariance signs are retained. It holds for every deterministic
dyadic subset, with no mean-cap argument and no asymptotic premise.

The homogeneous specialization is proved too. For every integern>=2,
0<=p<=1 and arbitrary realbeta,c2, the actual finite binomial pair
reference satisfies

    ||reference-Q(np,2c2-np^2)||_1
      <=4|beta-c2|+16exp(2)*
          (np^3+(np^2)^2+|c2|*(np^2+p)).

No upper bound onnp is assumed. A selected single pair in the full
finite heterogeneous theorem gives the exact covariance-reference
bound; the beta replacement has its proved cost4|beta-c2|. The source
natural subtractionn-2, omitted-product cardinality and all finite
products/sums are checked.

P1-MATH-0084 records the earlier removal of the logarithm and small-p
restriction. New P1-MATH-0086 records the independent removal of the
bounded-mean premise and the universal constant. This changes no
asymptotic exponent. Main15.1 remains in progress for the arithmetic
pair-activity rate A_2=O(N^(-2/3+epsilon)); companionT17.4 remains in
progress for C_2=O(a_N). Neither bound is assumed or counted proved.
Coverage77/167 (main28/73, companion49/94), confirmed findings86.
No external mathematical input, BCN premise, Paper C port, dependency
download, manuscript-byte change or Palomar registration is added.

Lean v4.36.0-rc2 full build passed (10655 jobs); actual axiom audit passed for all 6254 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 3971 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 15.77 GiB. The universal constant16exp(2) is proved for the actual finite heterogeneous Poisson–Charlier conversion, with no bounded-mean argument and every true Bernoulli marginal in[0,1]. Every contraction premise is discharged for actual probability factors. Actual original-run means, signed covariances and exact second cumulants are retained. The homogeneous binomial pair conversion has the same universal constant with no bound onnp. Arithmetic pair-activity and covariance scales remain open; main15.1 and companionT17.4 are in progress and add no proved coverage. Coverage77/167 (main28/73, companion49/94); confirmed findings86. No new external input, BCN premise, Paper C port, dependency download, manuscript-byte change or Palomar registration.
