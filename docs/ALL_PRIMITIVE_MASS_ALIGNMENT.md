# Conditional completion of companion T4.3 and T14.2

Sources: companion_sections/fixed_moments.tex:184 and companion_sections/cores.tex:260, including the literal ordered nominal sum and every cardinality in the joint-plus-centered sum.

Companion Proposition T4.3 and Theorem T14.2 are now complete
CONDITIONALLY under only the same chosen-source surface covers,
ordinary surface covers and uniform normalized-curve bounds
already required for15.2. Both printed exponents4/5 improve to1.
The entire literal fixed-order ordered nominal primitive sum
of T4.3 is bounded by N^(-1+epsilon), and the entire primitive
joint-plus-absolute-centered sum of T14.2, at ALL cardinalities
at least three, is bounded by N^(-1+epsilon).

DensePrimitiveTripleMassUnderInputs sums the ACTUAL one-source
two-target estimate proved in15.2. For every singleton source E,
the dense primitive extension rank mass is at most
(2*2^C/N)*N^(-1+eta), uniformly in E. The finite weighted source
cover uses all singleton subsets of the dyadic block; there
are exactly N. Every actual primitive triple has such a source,
and its remaining two centers are an actual pair in that cover.
The dense threshold is fixed at relative nullity L/4. Thus all
dense primitive triples together have mass N^(-1+epsilon).
No desired dense triple host count or target mass is assumed.

For the remaining primitive triples, relative nullity below
L/4 contributes at most2^((L+1)/4)<=K_C*N^(1/4).
The unconditional actual independent half-count contributes
N^(-3/2+eta), so their rank mass is N^(-5/4+eta), stronger than
the required power one. FixedPrimitiveMassUnderInputs combines
the two classes and proves rank mass<=N^(-1+epsilon) for EVERY
actual primitive triple population in the dyadic block. Local
irregularities, overlaps and zero marginals remain included.
For every fixed order r>=4, the earlier unconditional
N^(1-r/2+epsilon) primitive estimate already gives power at
least one. Consequently every fixed primitive order r>=3
has the stronger power one, with geometry needed only for
the three-window dense branch.

WeightedPrimitiveMass defines the exact u^card(I)-weighted rank
mass, and the actual joint-plus-absolute-centered mass. The
primitive relative nullity is at most L, so the rank mass is
at most2^L times the exact independent product with weights
u*p_x. Every primitive family is genuinely participating;
its full-support relation is proved. WeightedPrimitiveTail
uses the already uniform original participating tail with
a=2-epsilon/4 and its fixed size cutoff chosen before N.
Its independent mass is N^(-2+epsilon/2); multiplying by
2^L<=2^C*N and absorbing the fixed constant proves the
UNCONDITIONAL large-cardinality rank tail N^(-1+epsilon).
The relative-nullity amplification is included explicitly;
this is not merely an independent product estimate.

AllPrimitiveMassUnderInputs.uniform_rank combines that
uniform tail with only the finitely many fixed sizes below
its prechosen cutoff. The finite thresholds are maximized
after the actual finite geometric properties are supplied.
No fixed-order constant is evaluated at an order depending
on N. It proves the full rank-mass sum, including EVERY
cardinality and every actual dyadic primitive population,
is at mostN^(-1+epsilon). On the actual regular ground all
marginals are positive and nominal. The already proved
Fourier rank bounds give q(I)+|c(I)|<=2*rankWeight(I), for
compatible and incompatible systems alike. uniform_actual
therefore proves the stronger literal T14.2 bound; the named
companion_T14_2 also gives the exact printed power4/5.
No probability of an exceptional-window event is discarded.

FamilyEnumerationWeights bounds arbitrary nonnegative
family-dependent weights on any selected injective list
population by r! times its actual unordered family mass.
The finite fiber over each family has at most r! elements;
no constancy of nullity across different families is used.
PrimitiveOrderedMass defines exactly the actual distinct,
separated regular primitive lists of T4.3 and the literal
sum p^r*2^rho. Its membership theorem verifies all those
conditions. weight_formula identifies the nominal rank
weight with the actual heterogeneous primitive rank weight
ON THIS REGULAR population. rank_formula proves
rho=r*L-rank(sum of actual effective spaces).
The finite weighted enumeration inequality and fixed-order
factor absorption then prove the exact ordered T4.3
statement. No nominal-equals-actual-probability assertion
is made for incompatible systems or irregular windows.

The geometric Parameters and Hypotheses bundle contains
precisely the eight existing15.2 arguments, in the two target
orientations: chosen-source covers, ordinary covers and their
actual normalized curve bounds. Its cutoffs, degrees and
radical bounds are chosen by the existing dense two-target
theorem before the corresponding hypotheses. For the
all-cardinality result only a finite collection is used,
indexed below the already fixed tail cutoff. No new
geometric input, arithmetic mass assumption or axiom is
introduced. These properties themselves remain unformalized.

T4.3 moves from in_progress to conditional, T14.2 moves from
not_started to conditional. Unconditional numbered coverage
remains86/167; conditional results rise from18 to20. Finding
P1-MATH-0132 records the stronger primitive power one, the
short dense/low-nullity argument for triples, and the larger
unordered population without separation or local regularity.
No original manuscript byte, dependency, PaperC port or
Palomar registration is added. The sharper4/3 primitive tail
in main15.12 and the four-window branch of15.5 remain OPEN.

The JSON rows and finding132 record complete validation and the exact proof commit.
