# Actual original-law Poisson approximation under explicit BCN

Sources: the leading approximation in main 1.1, fixed factorial moments from main 6.4, and the exact stopped expansion from main 5.1. The optimal quadratic rate remains **in progress**.

The actual original count law now has a uniform qualitative Poisson
approximation, conditional on the existing explicit BCN plane-curve bound.
For every fixed critical-band width C and every tolerance epsilon>0 there
is one threshold N0 such that, for every N>=N0 and every critical length L,

    TV(Law(Z_N),Pois(mu_N)) <= epsilon,
    TV(Law(Z_N),Pois(lambda_N)) <= epsilon.

Here mu_N is the exact actual mean and lambda_N is the nominal mean. Both
Poisson references are actual normalized probability measures with singleton
masses exp(-mu)*mu^k/k!. Their parameters remain those of the current N,L;
no frozen limiting phase, fixed limiting mean, or convergence of the means
is assumed. Law(Z_N) is the actual pushforward law of the original infinite
prime-sign count, not a retained polynomial treated as a probability law.

The reconstruction argument is finite and unconditional before the arithmetic
moment estimates are inserted. For any finite Boolean family, write F_r for
its actual factorial moment and Delta=delta_1-delta_0. Its count law differs
from the finite polynomial sum_(r<k) F_r*Delta^r/r! in ordinary l1 by at most

    2^k * F_k / k!.

This follows from the already proved first-excluded-prefix expansion with
the hereditary cutoff |I|<k. Every boundary set has exactly k sites; its
suffix kernel stays positive and costs exactly its actual mass. Grouping
by cardinality identifies all coefficients with the actual factorial
moments. Comparing two such polynomials costs at most

    sum_(r<k) (2^r/r!) * |F_r-G_r|.

A new finite Banach-algebra estimate retains the factorial denominator:

    ||exp(x)-sum_(r<k) x^r/r!||
       <= ||x||^k * exp(||x||) / k!.

It is proved from the actual exponential series and the divisibility of
j!*k! into (j+k)!, not assumed as an interface. Applied in the completed
ordinary-l1 convolution algebra to x=mu*Delta, it bounds the Poisson
remainder by (2*mu)^k*exp(2*mu)/k!. Singleton coefficient comparison
transports the completed-norm bound to actual total variation. Universal
Poisson parameter stability TV(Pois(mu),Pois(nu))<=|mu-nu| is proved too.

For the actual original count, mu_N is uniformly bounded by M=2*2^C.
Choose the finite reconstruction order k AFTER epsilon, so that the
factorial tails for this fixed M are small. Only then assemble the
finitely many fixed-order moment estimates and choose N0. The original
moment of order k is bounded by mu_N^k+1, and the finite polynomial error
tends to zero by the checked fixed-order factorial estimates. The
convergent exponential series makes the reconstruction tails vanish.
No growing-order moment bound or target law approximation is a premise.

This proves leading Poisson approximation but not a quantitative TV rate,
the source optimal quadratic correction, its 4/3 remainder, or the exact
TV scale in main 1.2. Main 1.1 and 6.4 remain in progress; main 1.2 is not
counted complete. Numbered coverage remains 77/167 (main 28/73, companion
49/94); confirmed mathematical improvements remain 88. BCN is the same
ordinary explicit theorem argument already inventoried. No new external
input, axiom, dependency download, manuscript-byte change or Palomar
registration is introduced.

Verified Lean v4.36.0-rc2 full build (10809 jobs), actual Audit.lean kernel audit (6668 declarations; only propext, Classical.choice, Quot.sound), 4385 direct ledger/finding declaration checks, 138 source manifest entries and all 167 original statement hashes. Ubuntu root free space: 15.46 GiB. Finite factorial count-law reconstruction, the factorial Banach remainder and actual Poisson parameter stability are unconditional. Uniform original-law TV convergence to actual and nominal Poisson references uses the existing ordinary explicit BCN premise. Reconstruction order is chosen after tolerance and before N. No quantitative TV rate, optimal quadratic correction, new numbered completion or new mathematical finding is claimed. Coverage 77/167 (main 28/73, companion 49/94); confirmed improvements 88.
