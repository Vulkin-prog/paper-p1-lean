# Article Lemma15.4: actual several-small-kernel window counts

Source: `main_sections/exact_transfer.tex:202`, page41;
complete proof: `companion_sections/exact_transfer.tex:173–215`.

Article Lemma 15.4 is complete, with both literal source clauses
proved unconditionally for the actual complete dyadic windows.
It moves from not_started to proved. Numbered coverage is now
82/167. Confirmed mathematical improvements total 120; finding
P1-MATH-0120 records the endpoint A=2 and the weaker parameter
hypotheses actually proved. No source conclusion error is claimed.

CutoffSquareParts defines the full small-prime part s_Y(n), the
literal large square part a_Y(n)=product_(p>Y) p^(valuation_p(n)/2),
and d_Y(n)=s_Y(n)*a_Y(n)^2. This a_Y is not replaced by the
all-prime canonical square part. The exact decomposition
n=d_Y(n)*K_Y(n), quotient identity d_Y=n/K_Y, positivity and
divisibility are proved. Prime divisors of the small part are
at most Y; prime divisors of the large square part exceed Y
and divide n. Large square parts of distinct values at distance
at most Y are therefore coprime. Their coprimality with every
small part proves the exact lcm identity
lcm_i d_Y(v_i)=(lcm_i s_Y(v_i))*product_i a_Y(v_i)^2.
No squarefree replacement of these full prime powers is used.

PrimePowerAllocations assigns each complete prime power of a
positive modulus to one actual selected value that contains it.
Existence of that value follows from the factorization maximum
formula for a finite lcm. The resulting factors are pairwise
coprime, divide their actual values and have exactly the modulus
as product. This gives an actual SmoothModulusHosts certificate
whenever the modulus divides the lcm of actual positive values.
The construction does not assume a squarefree modulus or an
arithmetic assignment/count estimate.

ProductFirstPassage proves finite first-crossing statements for
indexed integer factors and for a factor list with a prescribed
initial product. Its smooth variant retains prime factors with
their multiplicities. SmallKernelCrossingCertificates applies
these to the actual quotients at bounded injective offsets.
If their lcm exceeds X and each a_Y(v_i)^2<=Z, it constructs
either a genuine square r^2 with X<r^2<=X*Z, or a genuine modulus
d with X<d<=X*Y and K_Y(d)=1. Each output carries the actual
pairwise-coprime CRT factors dividing the actual nearby values.
In the second branch, the complete product of large square
parts is kept as the initial product; only small-prime factors
are added. No ambient vector space or target counting assertion
is supplied as a premise.

SmallKernelLcmGrowth proves that m actual kernels at most N^beta
force the quotient lcm above C*N, for every fixed C>=0, when
m*(1-beta)>1. Each quotient is bounded below by a fixed positive
multiple of N^(1-beta). Its actual pairwise gcd is at most twice
the offset width. The finite product/lcm inequality and a proved
polylogarithmic absorption estimate give the strict growth.
The common threshold precedes the cutoff, width, centre and
every actual selected offset family. This is an unconditional
arithmetic estimate, not a quoted asymptotic input.

SquareCertificateCount counts the actual centres from square
certificates by enumerating their roots. The old fixed-modulus
CRT bound and the proved divisor subpower estimate absorb all
complete-prime-power allocations and bounded offsets. It has
one common threshold before the finite centre population and
all widths/interval endpoints. The already proved
SmoothCertificateCount counts the other branch: K_Y(d)=1
allows a Y-smooth factor times a square, with no requirement
that d itself be Y-smooth or squarefree.

SeveralSmallKernelCount combines these two actual populations
at X=2N. The square modulus has root at most
2*N^((1+u)/2) and polynomial height at most N^3 when u<=1.
The other modulus is at most 2*N*(log N)^A. Their union has
cardinality at most N^(max(1-1/A,(1+u)/2)+epsilon).
The selected offsets can vary with each actual centre after
the common threshold. No finite centre count is assumed.

SmallKernelWindowSets defines the actual small-value set inside
NormalizedWindowSets.values(x,L)=[x-1,x+L), the corresponding
severalWindows set and the actual twoWindows product-kernel set.
Finite subset selection gives m distinct actual values and
their bounded injective signed offsets. SmallKernelWindows
then proves the several-window count at the literal cutoff
floor((log N)^A), which represents exactly the primes above
the real threshold (log N)^A. On the critical band, this cutoff
eventually exceeds twice the complete window width. The second
source clause follows from the already proved actual two-kernel
product-cap count, at every H<=D*(L+1). It has the bound
#twoWindows<=N^(q+epsilon), simultaneously for every real q.
The joint theorem article_15_4 supplies one threshold before
every critical length, H and q. The source q>=0 is included.

The endpoint A=2 is covered: the square-smooth Rankin input
allows every sigma>1/2, hence the same N^(1/2+epsilon) modulus
count there. The several-window theorem only needs u<=1 and
m*(1-beta)>1; it uses no positive lower bound on beta or u.
These are the exact proved improvements in P1-MATH-0120.
For negative exponents, an impossible actual selection is
handled by the same statement rather than an omitted case.

This checkpoint adds no external literature property, Paper C
port, kernel axiom, dependency download or manuscript-byte edit.
It does not prove the separate sharp individual two-kernel
7/12 estimates in companion T1.5/T1.13, the Reuss-based input,
or the remaining primitive-mass and count-law reconstruction
results. Existing geometric conditional statements retain their
explicit unproved properties. Palomar remains deferred.

Full compilation, direct axiom audit, every ledger reference and the
proof-commit identifier are recorded in the JSON result row and finding120.
