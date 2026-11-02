# Main19.1: actual independent Poisson jumps and Hermite comparison

Source: `p1:cor:compound`. Status: **in progress** for the arithmetic admissibility and count-law rates. Original source bytes are preserved.

The actual probabilistic and analytic reference step of main19.1
is now proved. General jump-Poisson exponentials exp(b*(delta_j-delta_0))
have absolutely convergent series of actual atomic masses. Their
singleton coefficients are proved to be the pushforward of the actual
Poisson masses by n->j*n, for every naturalj including0. They define
actual probability measures for b>=0 and have completion norm exactly1.
The ordinary Poisson exponential consequently has norm exactly1 too.

The general compound reference pi_a*jumpPoisson(j,b) is proved equal
to the actual law of U+jV, where U,V are the coordinate maps on the
actual product of Poisson measures of meansa,b. Both coordinate laws,
their independence, every actual product singleton and the full
pushforward count law are proved. All series products, coefficient
transport, normalization and infinite tails are justified; none is
supplied as an input.

For0<=alpha<=mu, the Hermite reference is the actual probability law
of U+2V with independent meansmu-alpha andalpha/2, including both zero
parameter endpoints. Its completed reference factors exactly as

    H(mu,alpha)=pi_mu*exp((alpha/2)*Delta^2).

The exact source quadratic reference is identified as an actual signed
measure, and absolute Taylor tails give the explicit bound

    ||H(mu,alpha)-Q(mu,alpha)||_1<=4alpha^2 exp(2alpha).

The completed algebra inequality also holds for any realalpha when
mu>=0, with exp(2|alpha|); the probability interpretation requires
the stated nonnegative Poisson means. No small-alpha or upper-mean
assumption is used in this finite comparison. For every actual
probability lawP, a proved finite transfer gives

    TV(P,H)<=||P-Q||_1/2+2alpha^2 exp(2alpha).

No bound for ||P-Q|| is assumed or counted as a count-law approximation.

Actual exponential sums and Bochner integrals are also proved. The
general compound law has mean a+j*b and exponential moment

    exp(a*(exp(t)-1)+b*(exp(j*t)-1))

for every realt. The Hermite law has actual meanmu and exponential
moment exp(mu*(exp(t)-1)+(alpha/2)*(exp(t)-1)^2). Integrability is
proved before using each actual Bochner integral. These properties
concern the constructed reference, not the original run count.

The actual/truncated parameter admissibility at largeN, the numerical
law approximation, and the fixed-height hierarchy rates and leading
equivalents in main19.1 remain open. No matching lower bound for the
exact-parameter Hermite error is asserted. The source row is in
progress and adds no proved numbered coverage. Coverage77/167
(main28/73, companion49/94); confirmed findings remain85.
No new mathematical finding, external input, BCN premise, Paper C
port, dependency download, manuscript-byte change or Palomar
registration is introduced.

## Validation

Lean v4.36.0-rc2 full build passed (10647 jobs); actual axiom audit passed for all 6238 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 3955 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 15.78 GiB. Actual independent Poisson product coordinates, all natural jump sizes, absolutely convergent atomic series, exact coefficient pushforwards and norm-one probability exponentials are proved. The actual Hermite law has meanmu, every real exponential moment, factorization pi_mu*exp(alpha*Delta^2/2), explicit ordinary l1 error4alpha^2 exp(2alpha) and a finite TV transfer for any probability law. Integrability precedes all actual Bochner integrals. Eventual admissibility of model/truncated parameters and the source count-law rates remain open; main19.1 is in progress. Coverage77/167 (main28/73, companion49/94); confirmed findings85. No new finding, external input, BCN premise, Paper C port, dependency download, manuscript-byte change or Palomar registration.

Validated proof checkpoint: [78d568ce8f5c2a2e696d7b27570ed7ec587f6974](https://github.com/Vulkin-prog/paper-p1-lean/commit/78d568ce8f5c2a2e696d7b27570ed7ec587f6974).


## An eventual upper parameter gap under explicit BCN

The literal actual absolute pair mass A2 now has an unconditional finite
host reduction. The exact factor2 from unordered pairs to ordered tuples
is proved. Zero full pair loss forces zero covariance, including every
actual affine compatibility case. An injective tuple-to-host map gives

    2*A2(full)<=#full_loss_hosts*M+actual_host_independent_mass

wheneverM bounds actual joint masses of distinct pairs. The independent
term retains the actual heterogeneous products p_x*p_y. Every smaller
deterministic ground set has no greater absolute pair mass.

Under precisely the same explicit field-polynomial BCN argument already
used for main13.5,13.6,13.8, the checked actual host count N^(1+epsilon)
and actual pair cap N^(-3/2+epsilon) imply, uniformly before every
critical length and every deterministic dyadic subsetG,

    A2(G)<=N^(-1/2+epsilon),
    ||B2(G)-Q(actual_mean,actual_second_cumulant)||_1<=N^(-3/2+epsilon).

These are coarse rates. They do not supply the stronger manuscript
A2=O(N^(-2/3+epsilon)) or the optimal conversion exponent5/3, and they
do not compare the original count law with the retained reference.

The exact second factorial cumulant, including its negative diagonal
term, satisfies |alpha(G)|<=2*A2(G)+sum p_x^2. Its actual diagonal is
bounded byK^2/N using the proved critical marginal cap. The same BCN
argument therefore gives |alpha(G)|<=N^(-1/2+epsilon), and hence a
uniform eventually-small statement with the threshold beforeL andG.
No cumulant or activity bound is supplied as a premise of these rates.

Independently of BCN, the actual full count mean satisfies eventually

    (2^C)^(-1)/2<=mu<=2*2^C.

The lower bound uses the actual regular population, whose size is at
leastN/2, and its actual nominal marginal; the upper bound uses the
proved actual marginal cap. Under BCN this gives |alpha|<=mu/2 and
alpha<mu uniformly in the critical band. Nonnegativity ofalpha is NOT
proved here, so the remaining Hermite admissibility condition remains
open, as do the original and explicit-parameter approximation rates.

Main15.1 and19.1 remain in progress. Neither this weaker conversion nor
a partial parameter gap adds proved numbered coverage. Coverage77/167
(main28/73, companion49/94), confirmed findings86 unchanged. The only
unformalized input is the existing ordinary BCN argument, explicitly
passed at every dependent theorem. The finite host identities and the
mean bounds are unconditional. No new external estimate, PaperC port,
dependency download, manuscript-byte change or Palomar registration.

Lean v4.36.0-rc2 full build passed (10671 jobs); actual axiom audit passed for all 6305 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 4022 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 15.73 GiB. The exact finite2A2 host reduction and unconditional actual two-sided mean bounds are proved. Under the same explicit unformalized BCN argument, actual pair activity and actual second cumulants are at mostN^(-1/2+epsilon), actual conversion is at mostN^(-3/2+epsilon), and the upper parameter gap |alpha|<=mu/2 holds uniformly. No target activity, covariance or cumulant rate is assumed. Positivity ofalpha and the sharper source rates remain open; main15.1 and19.1 are in progress. Coverage77/167 (main28/73, companion49/94); confirmed findings86. No new external input, PaperC port, dependency download, manuscript-byte change or Palomar registration.
