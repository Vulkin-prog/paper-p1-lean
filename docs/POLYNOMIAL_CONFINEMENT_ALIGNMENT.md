# Polynomial confinement: construction and remaining point count

Source: companion_sections/confinement.tex:9, T8.1.

The auxiliary-polynomial construction in companion T8.1 is now
unconditional. T8.1 remains IN PROGRESS: the final nonlinear-curve point
count, O(B^(1/2+delta)) bound and little-o(B) conclusion remain open.

DivisorAuxiliaryPolynomialUniform.uniform_polynomial fixes d>=1 and
N0>=2 after C,tau>0 and fixed integers A,K>=1, BEFORE every N, critical
L, index TYPE, integer bases x,y, offset family(s_i,t_i) and composite
divisors g_i. The assumptions are |x|,|y|<=A*N, |s_i|,|t_i|<=K*(L+1),
pairwise coprimality, g_i>=N^tau, and divisibility of x+s_i,y+t_i.
The conclusion supplies an ACTUAL NONZERO rational polynomial P, with
both partial degrees<=d and total degree<=2d, vanishing at EVERY offset.
No index-cardinality bound, primeness or nonalignment is needed for
this construction. Fixed real comparison constants can be majorized
by integer A,K; nonalignment is needed later for the line count.

The (d+1)^2 rectangular monomials have quadratic dimension and linear
degree. choose_degree fixes 2d<tau*((d+1)^2-1), then absorbs all fixed
factorials and logarithmic powers into half the positive gap.
Replacing one integer evaluation row by the row at(-x,-y) produces a
determinant divisible by every OTHER g_i and hence their coprime
product. Its natural absolute value is bounded by
M!*X^(2d)*(B^(2d))^(M-1), M=(d+1)^2: the exceptional height X is paid
for once. All replacements vanish. The literal Cramer identity and
constant coordinate1 force every maximal evaluation minor to vanish.
The span/annihilator proof constructs nonzero coefficients and P,
rather than assuming them. Casts, row operations, determinant heights,
degree bounds and evaluations are checked. The generic annihilator
works over every field; its integral variant clears denominators of
a rational kernel to give a nonzero integral kernel.

The finite indexed divisor bound also keeps all point multiplicities:
pairwise coprime g_i>=N^tau dividing nonzero n with |n|<=N^beta have
cardinality<=beta/tau for N>1. If a*s_i+b*t_i=c, each g_i divides
a*x+b*y+c. This yields the same line cardinality bound when that
integer is nonzero and has the prescribed height. Deriving those two
line hypotheses uniformly from the source geometry remains pending.

No new unproved input or additional Paper C port is introduced. The
previously attributed logarithmic-factor bound is reused from its
existing checked P1 module. No numbered completion or new improvement
identifier is added:87/167 unconditional,39 conditional,151 confirmed
improvements. Dense primitive triples, dense nonaligned pairs, optimal
triple activity and the optimal quadratic upper rate remain open.
Original manuscript bytes, dependency pins and the Palomar milestone
are preserved.

The T8.1 JSON row records validation and the exact proof commit.


## Complete component count with explicit BCN dependency

Companion T8.1 is complete CONDITIONALLY on the already recorded
P1-GEO-BCN-PLANE-UNIFORM property, passed as the ordinary argument
PlaneCurvePointCount.UniformBound c kappa with c>0.
The source proof uses a fixed-degree Pila count. This checkpoint uses
the existing stronger BCN field property to supply that count;
it does NOT prove BCN, Pila, or a reduction from the separate
P1-GEO-NORMALIZED-CURVE-UNIFORM property. The unconditional auxiliary
polynomial construction from the preceding checkpoint is unchanged.

The actual indexed composite-divisor population now satisfies
#S<=M*(L+1)^(1/2+delta) for every fixed delta>0, and #S<=epsilon*(L+1)
eventually for every epsilon>0 when delta<1/2. The constant M and
threshold precede N, every critical L, every index TYPE and finite
indexed family. Coincident points retain their full multiplicity.
No divisor count, auxiliary polynomial or target confinement conclusion
is assumed. The divisor lower bound is nonstrict g_i>=N^tau.
The bases satisfy N<=A*x, |x|,|y|<=A*N with fixed integer A>=1,
and offsets have |s_i|,|t_i|<=K*(L+1) with fixed integer K>=1.
These comparisons encode the source asymptotic and offset constants;
integer upper bounds majorize arbitrary fixed real constants.
Only the first base needs a positive lower comparison. The second
base may have either sign. The source dyadic positive windows are
included. The no-line hypothesis is the literal nonvanishing of
(x+s_i)*(y+t_j)-(x+s_j)*(y+t_i) for DISTINCT offset points.

Every indexed collinear subfamily has cardinality<=3/tau after one
uniform threshold. If all its offsets coincide, the actual nonzero
common value x+s_i bounds its multiplicity. Otherwise an equation is
constructed from TWO ACTUAL grid points. Its coefficients are not
input data. Its base value is nonzero by the source no-line hypothesis
and has height<=N^3. Coprimality and divisibility give the indexed
3/tau bound. No defining-polynomial coefficient height is imposed.

BivariateFactorDegree proves the actual decomposition bounds over
every field. The sum of partial degrees is additive on nonzero
products and positive on nonunits. A polynomial with both partial
degrees<=d has at most2d normalized irreducible factors, each of
partial-degree sum<=2d. Every zero lies on one of those ACTUAL factors.
Normalization is chosen inside the finite proof, not as a mathematical
input. Rational degree-one factors have a literal rational linear
equation, and all their integer points are proved collinear.
A finite factor cover and an actual point-fibre cover retain every
index, including repeated offsets. The same collinear bound controls
both line components and every single-point fibre.

The existing BCN property gives a coefficient-uniform fixed-degree
bound #grid(Q,K*B)<=B^(1/2+delta), after one threshold before EVERY
irreducible rational factor Q with degreeSum(Q)<=2d and true total
degree>=2. It follows from the already checked source plane-bound
specialization and absorption of the actual logarithmic power.
Irreducibility over Q is exactly what the explicit property requests;
no unproved geometric-integrality test is silently added.
The auxiliary polynomial, its factors, line subfamilies and fibres
are all constructed in the proof. Applying the finite cover gives
M=(2d)*(3/tau). Its actual power bound gives little-o by choosing the
width threshold after the final tolerance.

afterExactAlignments is a literal finite filter removing every offset
which shares an exact line through(-x,-y) with a DISTINCT offset of
the original family. Equal-offset multiplicities are kept. Its
no-exact-line property is proved and the same power bound applies
with the SAME M,N0. The theorem also applies directly to any other
remaining subfamily satisfying the source no-line property.

No new external input, axiom, Paper C port or mathematical-improvement
identifier is introduced. T8.1 moves from in_progress to conditional.
Coverage is87/167 unconditional and40 conditional, with151 confirmed
improvements. Dense primitive triples T8.2, dense pairs T8.3, optimal
third activity and the optimal quadratic upper rate remain open.
Source bytes, dependency pins and the later Palomar milestone remain
preserved. The new dependency on the EXISTING explicit BCN property
is recorded rather than reported as an unconditional completion.


## Unconditional completion (P1-MATH-0402)

The full original T8.1 now has unconditional canonical power, little-o and post-alignment declarations in PolynomialConfinement. All indexed multiplicities, quantifier order and actual source comparisons above are retained. BoundedPlaneCurveCount.uniform_bound replaces the fixed-degree use of BCN with the fully proved checkpoint401 theorem; the full BCN property remains open. Earlier sections are historical validation checkpoints. See UNCONDITIONAL_POLYNOMIAL_CONFINEMENT_ALIGNMENT.md for the current scope.
