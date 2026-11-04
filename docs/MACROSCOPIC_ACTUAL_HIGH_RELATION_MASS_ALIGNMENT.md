# Actual macroscopic weighted high-channel profiles with the four-thirds error power

Companion T21.1, arithmetic_consequences.tex:26 and the high-height positive/signed estimates in its proof. All original source and statement hashes are preserved.

Companion T21.1 now has the ACTUAL weighted high-channel profile
bound on its literal macroscopic interval. Both the positive relation
weight and the absolute signed affine-compatibility weight have the
printed high-channel error power 4/3, with every growing height up to
B^3 and both coefficient orientations included. The leading height-
two channel and full profile equivalents remain open.

MacroscopicRelationPowers transports the proved actual pair-loss
bounds to literal powers 2^rho. For every fixed q>=1 and epsilon>0,
it proves 2^rho<=M^(1/q+epsilon) on every actual enlarged channel of
height at least q. The threshold precedes every moving positive
coprime coefficient pair, every source and target, and every height
up to B^3. Swapping both roots and coefficients covers the two
orientations. Zero-unit actual pairs have the separate subpower
bound 2^rho<=M^epsilon. The exact rational-unit power has a matching
height bound, with no upper height restriction in that finite part.

BoundedGeometricPairCount counts the original ordered channel hosts
on [2,M). The map(x,y)->(x,b*x-a*y) is injective at every positive a,
and gives the exact upper bound

  #channelPairs <= M*(2(a+b)B+1).

Every positive coefficient pair at height at most B^3 consequently
has at most 5*M*B^4 hosts. There are exactly B^6 coefficient pairs
before reducing or filtering heights. The entire finite union of
all those channels has at most 5*M*B^10 hosts. This is an actual host
count, with no assumed matrix or mass estimate.

MacroscopicHighRelationMass defines the actual macroscopic union
of all primitive channels whose maximum coefficient is at least q
and at most B^3. Both orientations and every original ordered label
are kept. This full mask contains its ordered separated subfamilies.
Its cardinality is bounded by the proved bounded-source count.
Summing the actual relation powers and absorbing the exact logarithmic
polynomial factor yields

  sum_high 2^rho <= M^(1+1/q+epsilon).

The positive weight 2^rho-1 is dominated pointwise by 2^rho.
For EVERY Boolean compatibility function eta on the actual pairs,
Lean also proves |eta*2^rho-1|<=2^rho, interpreting eta as 0 or 1.
Thus the same uniform theorem bounds the positive sum and the SUM OF
ABSOLUTE signed affine weights. The result is stronger than merely
bounding the absolute value of their total signed sum.

At q=3 this gives the exact high-channel power M^(4/3+epsilon)
needed by the macroscopic assertions of T21.1. The general q version
also keeps the higher-height exponents explicit. No homogeneous
probability or nominal-mean rescaling is used: the sums are literal
unweighted actual relation-code weights on the original interval.
All cutoffs, height choices, coefficient orientations, sources,
targets and Boolean compatibility functions follow the threshold.

P1-MATH-0203 records these actual weighted high-channel bounds.
Remaining work for T21.1 includes the fixed-height-two rational/full
comparison, the height-one separated contribution, actual positive
and signed channel translation sums, their distinct parity formulas,
leading equivalents and the parallel dyadic positive assertion.
Coverage stays 88 proved and 70 conditional out of 167, with nine
incomplete results. There are 202 improvements and one statement-
scope correction. No external input, kernel axiom, dependency,
compiler change or original manuscript edit is introduced.
Palomar remains deferred.
