# Source projective nondegeneracy for the elementary auxiliary-curve count

This checkpoint closes the algebraic nondegeneracy bridge in T1.4 Step 3.
It extends P1-MATH-0050, without a new numbered-result completion or a new
finding. Source: `p1:arith:reuss`, companion page 6,
`companion_sections/arithmetic_appendix.tex:139`; statement hash
`fb662a1d5ab5e605f53d3e8c90093d96c77b1157614bf68fc134d4487283c89b`.

## Coprimality of homogeneous forms

For two homogeneous degree-d binary forms, the source common-factor
condition means that every common divisor is a unit. Lean uses
`IsRelPrime F G` in Q[tau0,tau1]. It does not assume a Bezout identity
`IsCoprime F G` in this multivariate ring: two positive-degree forms
both vanish at the origin, so that stronger condition would be false.

`ProjectiveResultants` proves that any common divisor of the two
univariate charts homogenizes to a common divisor of the actual
degree-d forms. A unit maps to a unit under dehomogenization. This
gives univariate coprimality. If both chart degrees were below d,
tau1 would divide both padded forms. Evaluation at the origin proves
tau1 is not a unit, excluding this possibility. Thus one chart reaches
the padded degree, including the necessary condition at infinity.
The actual padded homogeneous resultant is consequently nonzero.

## Irreducibility supplies the common-factor condition

The auxiliary polynomial is represented literally as

    lambda0*F(tau0,tau1) + lambda1*G(tau0,tau1)

in the iterated ring Q[tau0,tau1][lambda0,lambda1]. A common divisor
of F,G gives a constant-in-lambda divisor of this polynomial.
Irreducibility says that divisor or its quotient is a unit. The
second alternative, after evaluation at lambda=(0,0), would make the
constant divisor zero and hence the auxiliary polynomial zero.
This contradicts irreducibility. The common divisor must be a unit.
No unique-factorization or analytic estimate is assumed in this argument.

## Actual homogeneous equations and coefficient heights

`HomogeneousCharts` defines the actual chart F(X,1), proves its degree
is at most d, and proves its degree-d homogenization equals F. Every
chart coefficient is the corresponding degree-d homogeneous coefficient;
coefficients above d vanish. Thus the coefficient height does not grow.
The actual integer resultant is transported injectively through Q.

`ProjectiveCurveCount.realSolutions` is defined directly by the two
primitive pairs, their actual homogeneous auxiliary equation, the
original bidegree-(ell,k) equation with nonzero integer right-hand side,
and literal real absolute-value boxes. Its equality with the previously
proved chart solution set is established. One threshold before all
forms, original coefficients, shifts and boxes gives

    #solutions <= N^epsilon * H

from fixed polynomial auxiliary height and either homogeneous
common-factor coprimality or irreducibility of the auxiliary polynomial
over Q. There are no separately assumed chart degrees or nonzero
resultants. The original coefficient forms and nonzero shift require
no height bound. The explicit finite single-resultant bound remains
available in the preceding checkpoint.

The source still needs auxiliary extraction and its polynomial height
from the determinant/lattice construction. The complementary
Heath-Brown bound in the eliminated pair height, other curve cases
and short-vector sums remain open. Full T1.4 is in progress and
coverage remains 54/167. No new unproved literature input, Paper C
port, manuscript revision or Palomar registration is introduced.

The full build passed (9,509 jobs), the actual axiom audit passed for
all 3,753 declarations, and Lean checked all 1,468 distinct
coverage/finding names. Only propext, Classical.choice and Quot.sound
occur; original manuscript bytes are unchanged.

Validated projective nondegeneracy checkpoint (9,509 build jobs;
3,753 audited declarations; 1,468 directly checked names):
[f8cc5d409f099f7440d9346f576605130073bc21](https://github.com/Vulkin-prog/paper-p1-lean/commit/f8cc5d409f099f7440d9346f576605130073bc21).
