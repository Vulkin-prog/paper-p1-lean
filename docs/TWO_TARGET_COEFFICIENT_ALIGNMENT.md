# Actual coefficient enumeration above fixed sources

Source: `companion_sections/exact_transfer.tex`, coefficient-enumeration paragraph in the proof of article15.2 (`main_sections/exact_transfer.tex:129`).

The actual two-target coefficient enumeration in the proof of
article Lemma15.2 is now proved unconditionally, with a common
source-dependent pool before every target, recovery subspace and
nonzero label. The lemma remains in_progress: the dense pair host
counts and their weighted summation are still open. Completed
numbered coverage stays82/167. P1-MATH-0121 records the stronger
whole-label-class source-cover argument, bringing confirmed
mathematical improvements to121 without a source-conclusion error.

OddLabelCircuitSupport removes ALL occurrences of a nonzero
label alpha from an actual binary prime row in which its
multiplicity is odd. The remaining labels sum to alpha. A proved
short physical representation chooses a support D containing no
alpha label; therefore D has at least two elements. Adding one
alpha occurrence gives a sum-zero support F of at least three
distinct physical blocks. With only two free blocks, F contains
an actual fixed source. This is proved for the literal finite
prime row, including repeated occurrences of alpha elsewhere
in that row. Neither a pairing of equal labels nor a nonzero
relation on just the two targets is assumed.

TwoTargetPrimeClassSupports applies this fact to the actual
prime-valuation rows of PhysicalWindowRelations.code, indexed
by the s fixed source blocks and two free target blocks.
For p>H>=L+1, the already proved row equations and one-occurrence
per physical block give all finite hypotheses. If p has odd
valuation in a whole nonzero label-class product, the class's
row multiplicity is odd. A short support in its actual bounded
pool then contains a fixed source value divisible by p.
The two free targets may overlap or have exact contacts.
No affine compatibility or local full-rank premise is used.

PhysicalSupportPoolBudget proves an individual physical size
bound for EVERY potential short support. If its distinct label
image has at most d elements and each label fibre has at most K
coordinates, its size is at most d*K. Consequently all potential
supports through a class of at most K coordinates have total
count at most K*supportBound(d,t,K), and each has size at most
d*K+1 after inserting the marked class coordinate.

TwoTargetClassSourceCover takes the union of the SOURCE
coordinates in all those potential supports, together with
the source coordinates already in the class itself. Its
cardinality is bounded by the explicit fixed constant
  K + K*supportBound(d,t,K)*(d*K+1),
where K=t-1. This construction enumerates no prime assignment.
For d=s+1, the actual large odd kernel of the class's two-target
product divides the product of the actual source values in
this bounded cover. A prime already dividing the class source
product is included immediately; every other odd target prime
is odd in the whole class product and is covered by the proved
source-support theorem. All source values and divisibilities
are literal positive window integers.

SourceSupportedCoefficientPool defines a finite pool from all
source-coordinate subsets of bounded cardinality, divisors of
their actual products and divisors of the small-prime primorial.
Whenever the large odd kernel of an actual positive integer n
divides one such source product, its FULL squarefree kernel
belongs to that pool and provides the exact integer equation
IsSquare(D*n). There is no assumed square-equation coefficient
or target counting bound. SourceSupportedCoefficientCount then
proves the pool has at most N^epsilon entries uniformly on the
critical band and at every H<=D*(L+1). Bounded source-coordinate
choices cost a fixed polynomial in L+1. Source products have
fixed polynomial height, as does the primorial by its elementary
4^H bound. Proved divisor subpower estimates absorb all three
factors. The threshold precedes every actual source tuple.

TwoTargetClassCoefficients identifies the bounded cover with
actual indices among the s source windows. Its explicit
sourceBound(s,t) is independent of N, target centres, label,
effective relation subspace and choices of divisors. Every whole
nonzero class gives a coefficient in the SAME pool. Its full
squarefree target-product kernel has height at most N^(2K)
when the class contains at most K actual coordinates in the
dyadic critical windows. The coefficient is positive and its
product with the actual target-value product is an integer square.

TwoTargetCoefficientEnumeration.uniform_enumeration supplies
these conclusions simultaneously. Fix s,t,D,C,epsilon with
t>=2. Then choose one threshold before N,L,H, the source tuple,
both free targets, EVERY actual recovery-regularized physical
relation subspace M and EVERY nonzero coordinate label. For
each fixed actual source tuple, one coefficient list of size
at most N^epsilon contains all of their squarefree target-product
kernels, each positive and at most N^(2*(t-1)), with its exact
square equation. Arbitrary contacts and irregular windows are
allowed. No binary graph, deletion pattern, subspace pool,
or prime-by-prime assignment is enumerated in this coefficient
stage. This stronger auxiliary formulation is P1-MATH-0121;
it is not a claim that all later geometric selection steps
can already be omitted.

Stable internal input P1-ARITH-TWO-TARGET-COEFFICIENTS is proved.
The remaining bridge from the lifted effective relation space
to a physical-code subspace, the exclusion of weak aligned
small-curve alternatives, the two mixed/univariate count strata
and their weighted dense-pair mass are not completed here.
The current result supplies their actual arithmetic coefficient
pool; it does not assume any of their desired host counts.
There is no new external literature assumption, kernel axiom,
Paper C port, dependency download or manuscript-byte edit.
Palomar remains deferred.

The JSON result row and finding121 record full compilation, the direct audit, every declaration reference and the exact proof commit.
