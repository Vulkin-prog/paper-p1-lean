# Ordinary correction and boundedness clauses of main Theorem6.4

Source: main_sections/fixed_moments.tex:152. The actual Touchard correction and all fixed ordinary moment bounds are proved here; arbitrary higher factorial cumulants are still separate work.

Main6.4 now also has its exact ordinary Touchard correction and uniform
boundedness of every fixed ordinary moment under the same three existing
finite geometric properties. The ordinary remainder is stronger, with
exponent1 instead of4/5, on every actual dyadic subground. Finding141 is
EXTENDED to the factorial AND ordinary moment corrections; it is not counted
a second time. Main6.4 remains IN PROGRESS until arbitrary higher factorial
cumulants and the optional nominal-parameter reformulation are checked.
Numbered coverage stays87/167 unconditional and25 conditional; confirmed
improvements stay141.

TouchardCountMoments.touchard is the actual finite Stirling polynomial.
ordinary_eq_factorial transports the exact natural power/falling-factorial
identity to the actual infinite count moments. poisson_hasSum proves that
its evaluation is the ordinary moment of the genuine Poisson mass sequence,
using the completed actual Poisson factorial-moment sums. second_derivative
uses the actual iterated polynomial derivative and the exact descending
factorial/choose identity. Thus the correction really is a_G*T_r''(mu_G)/2,
not a separately named surrogate polynomial. count_zero proves the actual
order-zero moment equals1, including the empty ground.

TouchardApproximation.finite_bound transfers any finite collection of exact
quadratic factorial errors to the ordinary correction, with the explicit
sum of nonnegative Stirling coefficients as its factor. FixedMomentInputs
packages precisely the previously listed five finite coarse/pair geometric
arguments; its Hypotheses fields contain ONLY those geometric properties.
No desired moment estimate is included. Its uniform_fixed theorem is a
proved wrapper around the completed actual factorial correction.

FixedQuadraticOrdinaryMomentsUnderInputs.uniform_fixed selects the finite
geometric bundles for all factorial orders up to the prescribed r BEFORE N.
It proves the order0 and1 corrections exactly, takes a common maximum of the
finitely many actual thresholds, and absorbs the fixed Stirling coefficient
sum. It gives the literal Touchard conclusion with remainder N^(-1+epsilon)
for every fixed r>=0, every critical length and every actual dyadic subground.
All exact actual means, diagonal corrections, zero marginals and affine
incompatibility are preserved.

FinitePairActivityInputs packages the already proved entire sharp pair
activity bound into one existing finite pair-input bundle with source
capsizeCap(1/100). Its uniform_cumulant theorem combines that rate2/3 with
the full squared-marginal diagonal sum to prove the same rate2/3 for the
absolute exact second factorial cumulant, on all actual dyadic subgrounds.
The reused diagonal inequality is itself unconditional; no BCN hypothesis
is assumed in either new theorem. This provides the required boundedness
of the exact quadratic parameter independently of the final law approximation.

BoundedFixedMomentsUnderInputs.uniform_factorial combines the exact
quadratic factorial correction at a fixed positive error margin, the
second-cumulant decay and the unconditional actual mean cap to obtain a
constant uniform factorial-moment bound. uniform_ordinary applies the proved
finite power/falling-factorial inequality to obtain the corresponding
ordinary bound at every fixed r>=2. uniform_low handles r=0 and1 without any
geometric hypothesis, from the exact zero moment and actual mean cap.
No Poisson approximation theorem is used to prove moment boundedness.

This checkpoint adds6 modules,13 theorems and3 definitions/structures.
The all-order factorial-cumulant conclusion is still separate work. No new
literature property, axiom, original manuscript edit, dependency download,
Paper C port or Palomar registration is added.

The JSON main6.4 row and extended finding141 record full validation and its exact proof commit.
