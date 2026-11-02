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
