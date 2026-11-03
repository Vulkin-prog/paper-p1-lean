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
