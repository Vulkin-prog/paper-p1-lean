# Moderate portion of main15.11

Source: main_sections/exact_transfer.tex:706, first mass conclusion.

The moderate arithmetic and all-order mass budget in main15.11
is now formalized for every fixed positive integer t. Main15.11
moves to in_progress: its saturated-family conclusion and the
general physical relation-to-saturation bridge remain OPEN.
Unconditional numbered coverage86/167, conditional coverage20,
and confirmed improvements132 are unchanged.

MultiAnchorValues uses ACTUAL t distinct offsets in one dyadic
window. The corresponding truncated odd kernels are pairwise
coprime because their prime factors exceed the window width.
Their product Q is squarefree, positive and at most(3N)^t.
For unmarked anchors it exceeds T^t. Every prime factor of Q
belongs to one actual selected value and is larger than Y.
MultiAnchorPrimeBudget proves the literal ceiling bound
m_t=ceil(t*log(3N)/log(Y)) on the number of these primes.

MultiAnchorModuli proves at most t receiving moduli exceed N
whenever their positive product is at most(3N)^t and N>3^t.
This threshold depends only on the FIXED anchor count, never on
the family order. The exact CRT product cost is at most
(6B)^t*2^(r-1)*N^(r-1)/Q. MultiAnchorAssignments obtains this
cost for actual center tuples from the existing prime-assignment
codes and literal congruence fibers; no count is assumed.
The number of assignments is at most(rB)^m_t.

MultiAnchorTupleCover counts the r*N*B^t choices of anchor
coordinate, dyadic center and ordered distinct offsets.
MultiAnchorCertificateCount.HasCertificate requires actual odd
prime membership in the receiving window for EVERY prime of Q.
The finite source tuple bound, uniform in every order r>=1, is
6^t*r*B^(2t)*2^(r-1)*N^r*(rB)^m_t/T^t.
Injectivity is retained and proves the source population is
empty when r>N. The empty-order population is also empty.

MultiAnchorWeightedSeries gives the actual convergent sum over
ALL orders with coefficient a^r/r!. Its finite majorant is
(6^t/2)*B^(m_t+2t)*(m_t+1)!/T^t
times exp(exp(1)*2aN). MultiAnchorOrder proves
m_t*loglog(N)/log(N) tends to t/A for Y=(log N)^A.
MultiAnchorFactorialBudget proves, uniformly for B<=D*log N,
B^(m_t+2t)*(m_t+1)!<=N^(2t/A+epsilon).
The all-order moderate mass is consequently
N^(-t*b+2t/A+epsilon) for T=N^b and any a>=0 with aN<=M.
MultiAnchorCertificateAsymptotic proves this before every
width B and weight a. Its critical-band specialization uses
the exact nominal marginal, with a fixed independent weight.

MultiAnchorFamilyMass recovers the actual factorial divisor by
counting EVERY injective enumeration of each certified family.
Certified means every enumeration has an actual moderate
certificate; it does not assume the desired mass estimate.
The finite layer and all-cardinality inequalities retain
arbitrary nonnegative heterogeneous weights p_x<=a.
MultiAnchorModerateMass.uniform_bound proves their literal
unordered independent product mass is at most
N^(-t*b+2t/A+epsilon), uniformly over every dyadic family
population, all critical-band lengths and all weights bounded
by M/N. No separation, regularity or positive-marginal premise
is used. Contacts and zero weights remain included.

This establishes the moderate certificate calculation with
all quantifiers and factorial costs. The next step must still
construct the t-anchor saturation graph, prove both directed
degrees, and connect actual block-dependent relation witnesses
to the certificate-or-edge alternative. No saturation-tail
bound or completed main15.11 result is claimed here.
No new geometric input, axiom, dependency download, Paper C
port, manuscript-byte change or Palomar registration is made.

The JSON result row records full validation and its exact proof commit.
