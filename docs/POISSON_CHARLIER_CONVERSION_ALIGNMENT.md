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
