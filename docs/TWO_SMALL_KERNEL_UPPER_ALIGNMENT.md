# Two individually small odd kernels: an elementary upper bound

An unconditional elementary upper count for two individually small odd
kernels is now proved on the literal complete windows. For every fixed
epsilon>0, one threshold precedes every T>=0, cutoff H<=D*log N and
length with L+1<=E*(log N)^A and L<=N. The actual window count is at
most (T+N^(2/3))*N^epsilon. In the critical band, H=B=L+1 and T=N^beta
give the upper exponent max(beta,2/3)+epsilon for every real beta.
Together with the previously proved all-cutoff lower count, this
establishes the sharp exponent beta for 2/3<=beta<1. This is a complete
subregime of companion T1.5, rather than its full 7/12 conclusion.

The proof makes a different use of the source elementary congruence
calculation. Fix the two actual small-prime odd supports and a positive
shift h. The canonical square parts d,e give divisibilities c1*d^2|n
and c2*e^2|n+h. An injection into actual integer linear fibres proves
the finite bound X*h/(c1*c2*d^2*e^2)+1 up to height X. The individual
kernel bounds imply c1*d^2,c2*e^2>=N/(2T) for n>=N/2. Summing their
reciprocal weights gives the explicit bound 24*h*T plus the number of
distinct actual square-part pairs, for n<=3N. This uses a finite
reciprocal-square tail bound 2/A for every positive real lower endpoint
A, including A<1. No dyadic subdivision of d,e is needed.

Split at P=ceil(N^(2/3)). Below P, the proved positive product-pair
count bounds the number of actual square-part pairs by P*N^epsilon.
Above P, the proved identity K_H(n)*K_H(n+h)*(d*e)^2<=n*(n+h)
forces the ACTUAL kernel product to be at most 16*N^(2/3). Only this
large-square sector is passed to the earlier product-cap count. The
argument never substitutes a product cap for the two individual bounds.
Small-prime support counts, the shift, the number of window offsets
and all constants are absorbed uniformly. A literal finite offset
cover and an injective translation identify the actual window count.

This is P1-MATH-0102: a Reuss-free upper estimate uniform in the real
kernel threshold, with explicit finite weighted fibres and an exact
sharpness subregime. It complements P1-MATH-0100. The full source
upper exponent max(beta,7/12), and sharpness on 7/12<=beta<2/3,
remain open. T1.5 stays in_progress and coverage stays 79/167.
There is no new external input, dependency change or manuscript
conclusion error. The original sources remain byte-for-byte unchanged;
Palomar remains a later milestone. There are now 102 improvements.

Verified with Lean v4.36.0-rc2: full lake build (11311 jobs), actual Audit.lean kernel-axiom audit (7674 declarations; only propext, Classical.choice, Quot.sound), all 5391 ledger references, source integrity (138 manifest entries / 167 numbered results), and git diff --check. Ubuntu root free space: 14.50 GiB.
