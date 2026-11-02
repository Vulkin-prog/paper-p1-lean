# Main15.1: exact heterogeneous analytic conversion

Source: `p13:transfer:conversion`, `main_sections/exact_transfer.tex:80`. Status: **in progress** for the arithmetic pair-activity rate. Original source bytes are preserved.

The full finite analytic statement of main15.1 is now proved for
actual signed measures, with the explicit constant C_M=16exp(2M).
The restriction p_*<=1/4 is unnecessary for this step: every actual
Bernoulli marginal in0<=p_i<=1 is allowed. A nonnegative P only needs
to dominate the marginals; it need not be small. Pair weights may have
either sign, and any selected family of two-element subsets is allowed.
No independence or covariance-sign assumption is used.

The new generic real Banach-algebra estimate is

    ||prod(1+v_i)-prod exp(v_i)
       +(sum v_i^2/2)*prod exp(v_i)||
    <=(2*sum||v_i||^3+(sum||v_i||^2)^2)*exp(sum||v_i||).

It follows by exact insertion identities, absolute exponential Taylor
tails and finite-product norm bounds. There is no logarithm or
small-norm restriction. The first-order estimate and deletion of any
actual two Bernoulli factors are also proved. Exact exponential sums,
scalar sums and pair corrections identify the resulting reference with
the actual Poisson–Charlier signed measure.

Writing mu=sum p_i, s_j=sum p_i^j, C_2=sum c(e),
A_2=sum|c(e)| and alpha=2C_2-s_2, the full finite bound is

    ||B_2-Q(mu,alpha)||_1
      <=16exp(2M)*(s_3+s_2^2+A_2*(s_2+P)),

whenever mu<=M. The actual ordinary sum of absolute singleton masses
is bounded, including its infinite tail. All covariances retain their
signs before taking this final norm, including incompatible pairs.
The exact finite reference and its completed-algebra image are proved
equal; no coefficient, convolution or tail identity is assumed.

The actual original-run specialization uses exact infinite-model
Bochner marginals and centered pair coefficients on every deterministic
subset G of the dyadic block. The exact identity

    secondFactorialCumulant(G)=2*sum c(e)-sum p_x^2

is proved from actual factorial moments, the finite subset formula and
the full square expansion. Thus the signed reference uses the actual
count mean and actual variance-minus-mean parameter, with its diagonal
term retained.

All actual marginals are proved in[0,1]. The already proved critical
local cap gives p_x<=2^(C+1)/N; its sum gives the actual mean bound,
and every power-sum substitution is proved. One threshold before all
critical lengths and all deterministic subsets gives

    ||B_2-Q(actual mean,actual second cumulant)||_1
      <=K_C*(N^(-2)+A_2/N).

This applies in particular to the full admissible set, with no
zero-marginal replacement or local-independence assumption. The
remaining source application requires A_2=O(N^(-2/3+epsilon)). That
arithmetic estimate remains open and is not supplied as a hypothesis
or counted as proved. Main15.1 is in progress for that final numerical
rate. Coverage remains77/167 (main28/73, companion49/94).

This extends P1-MATH-0084 to heterogeneous marginals without adding a
separate finding: confirmed findings84. No external mathematical
input, BCN premise, Paper C port, dependency download, manuscript-byte
change or Palomar registration is introduced.

## Validation

Lean v4.36.0-rc2 full build passed (10631 jobs); actual axiom audit passed for all 6169 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 3886 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 15.81 GiB. The full finite heterogeneous conversion is proved with C_M=16exp(2M) for every true marginal in[0,1], with arbitrary signed pair weights. Actual infinite-model means, centered pair coefficients and the exact second factorial cumulant with its diagonal correction are identified. A uniform actual bound K_C*(N^(-2)+A_2/N) holds before every critical length and deterministic dyadic subset. The source numerical rate remains open for the arithmetic pair-activity estimate; main15.1 is in progress. Coverage77/167 (main28/73, companion49/94); confirmed findings84, extending P1-MATH-0084 without a new finding. No external mathematical input, BCN premise, Paper C port, dependency download, manuscript-byte change or Palomar registration.

Validated proof checkpoint: [a7ccc5acd2065b4c3cb25f9a42022a3f1774dd0b](https://github.com/Vulkin-prog/paper-p1-lean/commit/a7ccc5acd2065b4c3cb25f9a42022a3f1774dd0b).
