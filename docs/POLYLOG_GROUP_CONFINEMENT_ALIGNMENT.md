# T21.4: three-dimensional support-group confinement

The full three-dimensional support-group branch of companion
T21.4 is now proved on actual finite tuple populations. The
individual-prime branch and the fixed-affine-plane variant
remain open, so the numbered proposition moves from not_started
to in_progress, not proved. Coverage stays 80/167 and confirmed
improvements stay 116; this is a proof-composition advance.

ProductConfinement proves the deterministic finite argument.
If all selected k-products of a finite factor set are <=N,
at most k-1 factors exceed N^(1/k). If the remaining product
exceeds N, a minimum-cardinality crossing subset has product
in (N,N^(1+1/k)] and all its factors are <=N^(1/k). Otherwise
the count of factors>Y is at most floor(log N/log Y), proved
by the actual finite logarithm-of-product identity. These
claims require neither primality nor an assumed stopping rule.

TernaryValueConfinement applies this to the actual group-value
pool. Group values and support labels have the same cardinality
by actual active-value injectivity. Their pairwise coprimality
is proved, every selected product is bounded by the actual top
product, and the crossing subset is shown to provide genuine
integer-offset CRT certificates for its actual centers.

CRTSupportCover canonically enumerates a finite set A of factor
sizes, rather than paying for all their orderings. The offset
cost is exactly (2R+1)^(3*card A). A certificate product Q>N
in a box of side DN has at most (D+1)^3 centers for each offset
assignment. The actual finite cover over all such A is bounded
by (D+1)^3 times the literal integer-factor weighted count of
T21.3. Coprimality is retained while applying CRT and only then
dropped in the positive Rankin sum. No target count is assumed.

RankinCertificateCritical combines that actual cover with the
already proved T21.3 integer-factor bound and the verified
sublinear-logarithmic exponential estimate. For any fixed
0<zeta<1 and k>=1 its count is at most
N^((1+1/k)*(1+(2+zeta)/c)+epsilon), uniformly over critical
lengths and bounded radii, all center base intervals and all
actual integer factor subsets. PolylogConfinementScales chooses
zeta and k before N so the extra exponent is arbitrarily small.
It also proves, uniformly in the critical band, that
k-1+floor(log N/(c log B))=o(L), with a literal statement for
every positive comparison constant and B=L+1.

TernaryGroupConfinement proves the actual exceptional-center
count N^(max(6/5,1+2/c)+epsilon). The first population has actual
topProduct>N and is counted by the completed T1.16. Every point
in the second population supplies an actual crossing certificate
and belongs to the Rankin cover. The two populations cover the
entire excessive-group family. The integer k depends only on
c,epsilon and precedes C,D, the actual sets and cutoff choices.
The source cutoff has no upper bound here.

LabeledPopulationCount proves a general finite label-fiber count.
TernaryConfinementMass uses it to include B^J actual offset-pattern
labels, with one threshold before the label type, all arithmetic
assignments and nonnegative weights. For point weights at most
N^(-beta+epsilon/2), the actual excessive-group population has
mass at most
N^(-min(beta-6/5,beta-1-2/c)+epsilon).
The remaining error margin pays for the count and labels. This
is the source's uniform N^(-beta+o(1)) weight regime made explicit;
it is not an assumed exceptional-count or exceptional-mass bound.
The actual exceptional finite set is defined, its mass is bounded,
and every retained tuple has at most
k-1+floor(log N/(c log B)) actual groups greater than B^c.

TernaryGroupNegligibility proves that c>6 makes
max(6/5,1+2/c)<4/3. It supplies a fixed positive point-weight
margin theta and a fixed k such that for every eta>0, eventually
the actual exceptional mass is <=eta*L*N^(-2/3), whenever each
host weight is in the beta=2 class, at most N^(-2+theta).
The retained count is the same literal source expression. This
is the sufficient c>6 assertion for the three-dimensional group
branch. No c>3 fixed-plane claim is made at this checkpoint.

The remaining T21.4 work is explicit: the individual-prime
fixed-k budget must account for repeated offset supports, and
the specified-plane CRT cover must enumerate only two free
offset coordinates to obtain the 1/c exponent and c>3 threshold.
No new literature input, Paper C copy, original source change,
dependency update or Palomar registration is introduced.

The exact validation and proof commit are recorded in the T21.4 JSON ledger entry.


## Individual primes and the common integer-factor cover

The individual-prime branch of companion T21.4 is now proved
in three dimensions, in addition to the previously completed
support-group branch. The remaining obligation is the specified
finite-family-of-affine-planes variant with its 1/c exponent
and sufficient c>3 threshold. T21.4 therefore stays in_progress;
numbered coverage stays 80/167. The two checked simplifications
below are P1-MATH-0117 and P1-MATH-0118, bringing the confirmed
improvement total to 118 without asserting a manuscript error.

TernaryIndividualPrimes constructs the actual finite pool of
primes above H with odd valuation in an actual value in every
block. Its membership is the literal existence of a support
triple in the actual pool. Each such prime is proved prime and
its support group active. A selected finite product of distinct
primes divides the product of its actual covering support groups.
If at most two support groups occur, the previously proved
one- and two-group bounds give a product <=2A(H+1). Thus three
selected primes above this threshold must occupy three supports,
and their product is at most the actual three-group top product.
This handles every repeated-support case without a new cross
product or collinearity proof. The large-prime tail reuses the
already proved actual three-group forced-plane count. This is
the unconditional proof simplification P1-MATH-0117.

FiniteFactorTopProducts proves the canonical largest k-product
for an arbitrary actual finite set of integer factors. It is
attained when positive, is zero when too few factors exist,
and a maximizing selection consists of the strictly largest
factors when they are positive. The smallest-factor deletion
inequality and its arbitrary real-exponent threshold consequence
are proved. No decreasing-order convention or induction target
is supplied as an input.

TernaryPrimeTopProducts constructs the actual individual-prime
top product, proves its height <=A^k and its monotonicity as the
prime cutoff increases, and constructs the actual offset-CRT
certificate of every positive maximizing selection. The prime
sizes are pairwise coprime because they are distinct actual
primes. Their offset supports may repeat. TernaryPrimeCounts
and TernaryPrimeWeakCritical prove the weak product count from
this literal certificate and the actual ordered-factorization
pool, with uniform critical-band absorption.

TernaryPrimeBudget proves the complete individual-prime fixed-k
budget N^epsilon*(N^3/T^2+N^(6/5)) for every fixed k>=3. Its
three-prime strong sector is bounded by the actual group sector
using the support-merging argument. The same N^(9/10) preceding
cutoff works throughout the strong induction. TernaryPrimeTheorem
retains arbitrary source cutoffs with no upper bound by the
already checked internal cap min(H,2R+1), and includes B^J
actual pattern labels with one threshold before the label type.
The source full even-map hypotheses are retained explicitly.

TernaryPrimeValueConfinement supplies the deterministic
confinement-or-certificate alternative for actual primes>B^c.
The crossing certificate belongs to the same integer-factor CRT
cover used for support groups. In particular, the separate
prime-only Euler product is unnecessary for the final T21.4
bound: use the proved integer-factor Rankin bound with any fixed
positive zeta, choose zeta small and k large before N, and absorb
the extra exponent in epsilon. The exponential in B^(1-zeta)
is uniformly subpolynomial. This is P1-MATH-0118; it simplifies
this application without replacing the sharper prime estimate
already proved in T21.3 or changing its statement.

TernaryPrimeConfinement proves the actual excessive-prime count
N^(max(6/5,1+2/c)+epsilon). TernaryPrimeConfinementMass counts
all actual pattern labels and proves the literal exceptional
mass N^(-min(beta-6/5,beta-1-2/c)+epsilon), for nonnegative
host weights in the source's uniform N^(-beta+o(1)) class.
The exact point-weight margin epsilon/2 is exposed. The actual
exceptional finite set is defined, its mass is bounded and every
retained tuple has at most k-1+floor(log N/(c log B)) individual
primes above B^c. The uniform o(L) conclusion follows from the
previously checked logarithmic-count scale theorem.

TernaryPrimeNegligibility proves the sufficient c>6 assertion
for beta=2, with a fixed positive point-weight margin and a
fixed k chosen before N. For every eta>0 the actual exceptional
mass is eventually <=eta*L*N^(-2/3). The argument is unconditional
within the explicitly stated positive-host-weight regime; it
assumes neither the exceptional population count nor its mass.

Only the fixed-plane 1/c and c>3 branch of T21.4 remains open.
No unproved geometric or analytic input is introduced by these
prime results, no further Paper C source is copied, and the
original manuscript and dependency pins remain unchanged.
Palomar remains deferred until the full work is complete.

The exact validation and proof commit are recorded in the T21.4 JSON ledger entry.
