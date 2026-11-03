# Multiquadratic split radicands: exact square-class independence

The square-class independence assertion at the beginning of Step 1
of companion T1.7 is now proved literally. Let F be ANY field of
characteristic zero, and use the fraction field of F[X][Y]. For a
family of integer root lists I_i,J_i, pairwise disjoint within each
coordinate list, and arbitrary nonzero constants c_i in F, the actual
square classes of
  c_i * product_(a in I_i)(X+a) * product_(b in J_i)(Y+b)
are linearly independent over F_2 whenever I_i or J_i is nonempty
for each i. The index type can be arbitrary; linear independence is
checked on every finite subfamily. In particular this applies over
an algebraically closed characteristic-zero base, not just over Q.

The proof uses the existing internal reflection of squares from a
fraction field to its integrally closed polynomial ring. Passing to
one coordinate fraction field makes the scalar and the other split
factor units; the remaining nonempty split factor is separable and
not a unit, so its product with this nonzero scalar is not a square.
Swapping coordinates covers an empty root list on either side.
Exact product identities identify a finite subfamily product with
the nonzero product scalar times the split word on the two literal
unions of its disjoint root lists. Every nonempty subfamily product
is therefore nonsquare. The existing actual field square-class
quotient and a proved binary coefficient argument turn this into
literal F_2 linear independence. Nonzero radicands are proved too.

There is no smoothness or coefficient-height hypothesis in this
algebraic assertion. These hypotheses were already unnecessary for
the source independence argument, so no new mathematical-improvement
identifier is assigned. This adds the checked algebraic independence
part of Step 1, rather than a multiquadratic surface point count.
The general coordinate-ring freeness, field/localization and finite
birational projection arguments, the surface covering, curve-degree
exclusions and the two-variable estimates remain open. T1.7 stays
in_progress, coverage stays 79/167 and confirmed improvements stay
104. No external determinant estimate is treated as proved, and no
dependency download, original source change or Palomar registration
is introduced.

Verified with Lean v4.36.0-rc2: full lake build (11333 jobs), actual Audit.lean kernel-axiom audit (7726 declarations; only propext, Classical.choice, Quot.sound), all 5443 ledger references, source integrity (138 manifest entries / 167 numbered results), and git diff --check. Ubuntu root free space: 14.45 GiB.


## The literal multiquadratic generic field and its degree

The generic multiquadratic field in Step 1 of companion T1.7 is now
constructed internally and proved to have degree 2^k. This advances
the previously checked square-class independence to a literal field
construction, rather than postulating an abstract extension degree.
For every commutative base ring and finite radicand list, a recursively
defined tower of actual quadratic algebras has an explicit free basis
indexed by one binary choice per equation. Over a nontrivial base its
finite rank is 2^k. The base embedding is proved injective, each actual
radical generator squares to its specified base radicand, and those
generators generate the entire algebra. A structural induction
principle is proved on the literal tower.

Over a characteristic-zero field, an exact one-step criterion says
that a base element g becomes square after adjoining sqrt(f), f!=0,
if and only if g or f*g is square in the base. This includes the
reducible one-step algebra as well. Induction proves a full descent
criterion for an independent radicand list: a base element g becomes
square exactly when g times the product of some selected sublist is
square in the original field. If every nonempty selected sublist has
nonsquare product, each successive radical remains nonsquare and the
literal tower is a field. No fieldhood or extension degree is assumed.

The source application uses the actual scaled split radicands over
Frac(F[X][Y]), for every characteristic-zero field F. Pairwise disjoint
integer root lists, at least one nonempty root list per equation, and
arbitrary nonzero constants prove the required sublist condition by
the already checked nonsquare finite-product theorem. Every finite
list of distinct equations therefore gives an actual generic field
of degree 2^k. This remains true when F is algebraically closed; no
smoothness or coefficient-height hypothesis enters this algebraic
step.

The explicit coordinate-ring quotient presentation and its embedding
in this generic field, the finite birational sum-of-radicals projection,
the projective and curve-degree arguments and the two-variable point
counts remain open. Thus this is further checked algebraic groundwork
for T1.7, not completion of the geometric count. T1.7 stays in_progress,
coverage stays 79/167 and improvements stay 104; the source already
uses this algebraic argument, so no new improvement identifier is
assigned. No external counting input, dependency download, original
manuscript change or Palomar registration is introduced.

Verified with Lean v4.36.0-rc2: full lake build (11341 jobs), actual Audit.lean kernel-axiom audit (7745 declarations; only propext, Classical.choice, Quot.sound), all 5462 ledger references, source integrity (138 manifest entries / 167 numbered results), and git diff --check. Ubuntu root free space: 14.44 GiB.


## The actual coordinate domain and the finite affine radical-sum projection

The actual split-radical coordinate algebra in Step 1 of companion
T1.7 is now proved to be a domain, and the affine sum-of-radicals
projection is proved finite. The construction continues to work over
every characteristic-zero base field F, including an algebraic closure.
It uses the literal tower over F[X][Y] of the actual scaled split
polynomials, rather than assuming geometric integrality of a surface.

First, the tower has its exact universal property. For every base
ring homomorphism R->A and every actual family x_i in A satisfying
x_i^2=phi(f_i), there exists a unique ring homomorphism from the
tower to A that agrees with phi on the base and sends each actual
radical generator to x_i. The corresponding algebra-point equivalence
is also constructed. An explicit two-coordinate quadratic ring map,
its uniqueness and a recursive lift prove this, including empty
systems and arbitrary commutative target algebras. Thus the tower
represents precisely the simultaneous polynomial equations. Evaluation
at actual values X,Y specializes this statement to the source split
system; the scaled-word evaluation formula is checked explicitly.

Next, an actual recursive base-change homomorphism is constructed for
every ring homomorphism R->S. It is proved to commute with the base
embeddings, and it is injective whenever the base homomorphism is.
The quadratic step keeps the literal new parameter and the proved
coefficient equality visible, avoiding an assumed localization map.
Specializing to F[X][Y]->Frac(F[X][Y]) embeds the coordinate tower in
the actual generic field already proved to have degree 2^k. This
proves the coordinate domain property for every disjoint root-list
system with nonzero coefficients and at least one selected root per
equation. No coefficient height or smoothness is used in this step.

Finally the image algebra of the sum-of-radicals map is defined as
R[sum_i sqrt(f_i)] and identified with the literal range of polynomial
evaluation at that sum. Since the entire coordinate tower is a finite
R-module, it is a finite module over this actual image algebra. The
radical sum is also proved integral over R. This establishes the
algebraic finiteness of the affine projection; its birationality is
NOT yet proved. The generic primitive-element argument, Krull and
projective dimensions and degrees, curve exclusions, surface covering
and all two-variable point estimates remain open.

These are exact internal algebraic parts of the source proof, with
no new improvement identifier. T1.7 stays in_progress, coverage stays
79/167 and improvements stay 104. No surface-counting estimate is
treated as proved, no new external input or dependency download is
introduced, and the original sources and Palomar status are unchanged.

Verified with Lean v4.36.0-rc2: full lake build (11351 jobs), actual Audit.lean kernel-axiom audit (7767 declarations; only propext, Classical.choice, Quot.sound), all 5484 ledger references, source integrity (138 manifest entries / 167 numbered results), and git diff --check. Ubuntu root free space: 14.43 GiB.


## The actual primitive radical sum and the birational affine projection

The radical-sum projection in Step 1 of companion T1.7 is now
proved birational in its literal algebraic sense. The inclusion of the
actual image algebra R[sum_i sqrt(f_i)] into the actual coordinate
tower induces a ring isomorphism of their fraction fields. The
isomorphism is proved to send every image-algebra element to that
same element in the source fraction field. Combined with the
previous finite-module theorem, this verifies the finiteness and
birationality of the actual affine projection.

First, each radical generator is identified with a distinct vector
of the explicit binary tower basis, proving their linear independence
over any commutative base ring. Every actual choice of radical signs
defines an algebra endomorphism by the already checked universal
property. Its square is the identity, so an actual sign automorphism
is constructed. In characteristic zero the sums for the 2^k sign
choices are pairwise distinct. Every such sum is a root of the
original sum's mapped minimal polynomial. The root count forces
degree at least 2^k; the tower dimension bounds it from above. The
minimal polynomial therefore has degree exactly 2^k, and its power
basis proves K[sum_i sqrt(f_i)] is the entire generic tower. The
independence hypothesis is discharged internally for the actual
generic split-radical family.

The recursive base-change map is proved to preserve the literal
radical sum. A general fraction-field lemma then identifies the
generic field as a fraction field of both the coordinate algebra
and its actual projection image: the subfield generated by the
base ring's image contains its fraction field K, and contains the
generic primitive sum, hence the whole generic extension. This
uses the actual injected ring maps and proves the extension on
every original element. It does not merely identify abstract
fields of the same degree or assume birationality as an input.

For the source system these statements hold over every characteristic-
zero field F, including an algebraic closure, for pairwise disjoint
integer root lists, nonzero coefficients and at least one selected
root per equation. Together with the previously proved coordinate
domain, free rank and universal point property, this completes the
algebraic integrality and finite birational projection assertions of
Step 1. The projective degree bounds on the image, Krull and
projective geometry, curve exclusions, surface coverings and the
two-variable host counts remain open. In particular the degree
2^k of the generic minimal polynomial is not yet counted as a proof
of the source projective-degree assertion.

These are internal proofs of the source algebra, with no new
mathematical-improvement identifier. T1.7 stays in_progress, coverage
stays 79/167 and confirmed improvements stay 104. No unproved
counting estimate, dependency download, original-source modification
or Palomar registration is introduced.

Verified with Lean v4.36.0-rc2: full lake build (11365 jobs), actual Audit.lean kernel-axiom audit (7793 declarations; only propext, Classical.choice, Quot.sound), all 5510 ledger references, source integrity (138 manifest entries / 167 numbered results), and git diff --check. Ubuntu root free space: 14.42 GiB.


## P1-MATH-0105 — A monic equation and a free power basis for the actual affine image

The actual affine image in companion T1.7 now has its literal
monic irreducible equation and an explicit free power basis over the
base polynomial ring. Write R=F[X,Y], A for the actual quadratic
tower and s for the sum of its k radical generators. The actual
minimal polynomial P in R[Z] is monic, has Z-degree exactly 2^k,
and generates the full kernel of evaluation Z->s. The quotient
R[Z]/(P) is identified with the actual image subalgebra R[s], with
the isomorphism proved on every polynomial. Thus this is a
presentation of the image, rather than a polynomial merely
vanishing on a collection of source points.

The general argument works over any domain R with a characteristic-
zero fraction field K for which the actual mapped radicands are
independent. Every nonzero annihilating polynomial over R has
Z-degree at least 2^k. The finite free coordinate tower bounds the
minimal polynomial degree from above. Its coefficient map to K is
the actual generic minimal polynomial. Monic division then reflects
divisibility from K[Z] to R[Z] and proves the complete kernel
identity. No integral-closedness hypothesis on R is needed.

Transporting the actual quotient's power basis gives
  R[s] free and finite over R, of rank 2^k,
  with actual basis 1,s,...,s^(2^k-1).
This strengthens the source's description of the affine image and
is recorded as P1-MATH-0105. The freeness concerns the image as an
algebra over the plane; the finite birational map from A to its
image is a different morphism. All coefficients remain arbitrary
nonzero constants, and no height or smoothness premise is used
for this algebraic assertion.

A concrete algebra equivalence transports the nested polynomial
to Mathlib's MvPolynomial (Fin 3) F. Its coordinate 0 is Z, 1 is Y
and 2 is X; the variable images and literal evaluation are checked.
The transported equation is irreducible and its actual totalDegree
is at least 2^k. Every actual solution of the original split
equations maps to its zero at (sum w_i,Y,X). The point statement
is obtained from the already proved unique source ring map, not
from an assumed point-count or geometric correspondence.

Finally the monic projection equation is proved to commute with
arbitrary base changes that retain the actual generic independence.
For every characteristic-zero field extension the actual scaled
split polynomials, root-list system and projection equation all
commute with the literal coefficient maps. The original image
equation therefore remains irreducible after every such extension,
including passage to an algebraic closure. This verifies the
coefficient compatibility needed for geometric irreducibility.

The uniform upper bound on the defining total degree, projective
closure and degree formulas, curve exclusions, surface coverings
and two-variable host estimates remain open. The totalDegree
lower bound proved here is not a completed projective intersection-
theoretic degree argument. T1.7 stays in_progress and numbered
coverage stays 79/167. Confirmed improvements total 105; no error
in a manuscript conclusion is asserted. No external counting
input, dependency download, source-byte change or Palomar
registration is introduced.

Verified with Lean v4.36.0-rc2: full lake build (11379 jobs), actual Audit.lean kernel-axiom audit (7836 declarations; only propext, Classical.choice, Quot.sound), all 5553 ledger references, source integrity (138 manifest entries / 167 numbered results), and git diff --check. Ubuntu root free space: 14.40 GiB.


## A universal integer equation and the coefficient-uniform image-degree bound

The actual defining polynomial of the split-radical image now
has both degree bounds needed in Step 1 of companion T1.7:
  2^k <= totalDegree(H) <= C(k)*max(1,K),
where each equation's two root lists have total size at most K.
The natural constant C(k) is defined as the actual total degree of
one fixed integer-coefficient universal polynomial. It depends only
on k, independently of the coefficient values, their heights,
smoothness, the selected integer roots, and the base field. This
also makes the upper dependence on the root-list degree linear.
The lower bound and the exact image presentation are the ones
already verified in the preceding checkpoint.

The proof constructs a literal tower over Z[T_1,...,T_k] and takes
the actual minimal polynomial of the sum of its formal radicals.
It is monic and has degree in Z at most 2^k by the already proved
finite free tower. Mapping T_i to the actual radicands specializes
this SAME polynomial to the actual image equation whenever the
target generic radicands are independent. The earlier base-change
theorem requires only independence in the target, so no unproved
generic square-class assertion about these universal parameters
is needed. The parameter-list map and every coefficient homomorphism
are checked on the actual rings.

The universal equation is transported to a multivariable polynomial
over Z, with one variable for the radical sum and k for the
radicands. Its literal evaluation in MvPolynomial (Fin 3) F is
proved equal to the actual image equation. A general support-sum
argument bounds the total degree of polynomial substitution by
the original total degree times the maximum substituend degree.
Each actual split radicand has lifted total degree at most its
two root-list sizes, and the sum variable has degree one. This
gives the displayed bound with no coefficient-height dependence
and no elimination or geometric estimate supplied as an input.

This extends P1-MATH-0105 with the fixed universal equation and
the linear-in-K degree bound. Its earlier free-power-basis finding
and validation are preserved in the history. Confirmed improvement
count remains 105, numbered coverage remains 79/167 and T1.7 stays
in_progress. The remaining work includes identification of the
projective closure's intersection-theoretic degree, the weighted
embedding and curve-degree formulas, surface coverings, curve
exclusions, and the actual two-variable host counts. No completed
projective or counting claim is inferred just from a total-degree
inequality. No external input, dependency download, original-source
change or Palomar registration is introduced.

Verified with Lean v4.36.0-rc2: full lake build (11387 jobs), actual Audit.lean kernel-axiom audit (7856 declarations; only propext, Classical.choice, Quot.sound), all 5573 ledger references, source integrity (138 manifest entries / 167 numbered results), and git diff --check. Ubuntu root free space: 14.39 GiB.


## The actual radical, Veronese-chart and projection point heights

The actual point-height assertion in Step 2 of companion T1.7
is now proved from the literal integer equations. If |X|,|Y|<=2N,
the selected offsets have absolute value at most N, each pair of
root lists has total size at most K, and |c_i|<=N^A, every actual
integer solution of
  w_i^2=c_i*product_(a in I_i)(X+a)*product_(b in J_i)(Y+b)
satisfies |w_i|<=3^K*N^D whenever A+K<=2D. Here the finite radical
bound allows real D; the common-coordinate theorem takes an integer
D for the monomial degrees. It retains signed coefficients, all
integer X,Y, zero factors and zero radicals.

For k equations a single positive constant
  C(k,K,D)=2^D+(k+1)*3^K
bounds the absolute values of every actual affine monomial X^aY^b
with a+b<=D, every w_i and their literal sum by C(k,K,D)*N^D.
These are precisely the affine coordinates underlying the weighted
Veronese chart at Z=1, together with the radical-sum projection.
The integers remain actual integer coordinates; no presumed geometric
height or abstract bounding-box hypothesis is substituted for them.

The finite proof first bounds the natural absolute value of each
integer split product and squares the actual radical equation.
Real power monotonicity converts the coefficient-height exponent
to the required D, and the triangle inequality controls the sum.
The monomial bound is proved separately on the actual integer powers.
An eventual version then handles offset bounds b*(log N)^r for
arbitrary fixed b,r: one threshold precedes every coefficient family,
root-list system, point and radical solution. In particular it covers
the logarithmic offsets in the source with the asserted uniformity.

This verifies the elementary height component of Step 2, while the
construction of the projective embedding and its degree and curve-degree
identities remain open. The curve exclusions, surface coverings and
two-variable host counts also remain open. T1.7 stays in_progress,
coverage stays 79/167 and confirmed improvements stay 105; no new
improvement identifier is assigned to this checked source height
calculation. No external estimate, dependency download, original
source edit or Palomar registration is introduced.

Verified with Lean v4.36.0-rc2: full lake build (11393 jobs), actual Audit.lean kernel-axiom audit (7866 declarations; only propext, Classical.choice, Quot.sound), all 5583 ledger references, source integrity (138 manifest entries / 167 numbered results), and git diff --check. Ubuntu root free space: 14.38 GiB.


## The actual selected-value obstruction on rational lines

The functional-square obstruction on affine rational lines in
Step 3 of companion T1.7 is now proved for the actual finite sets of
selected positive values. It uses their literal even-selection maps
and square-class spaces, rather than requiring independence of the
larger full windows. Two equations with disjoint nonempty first root
lists already suffice. The second selected set's even-selection map
need not be injective; the two actual even image spaces must remain
in direct sum. Coefficients are arbitrary nonzero rational constants.

The polynomial proof is explicit. A square polynomial has zero
derivative at each root. If a product c*P*Q is square, c!=0 and P
is separable, every root of P must therefore be a root of Q.
Applying this to the literal restriction Y=alpha*X+beta of each
scaled split equation forces every first-list root to match an
actual second-list root. Squares in the actual rational-function
field are reflected to the integrally closed polynomial ring before
this argument is applied. No root-matching statement is assumed.

The selected-value arithmetic is proved on arbitrary finite positive
integer sets S,T. Two distinct elements of S and a proportional pair
in T give the same nonzero even square class in both actual spaces.
Injectivity of the first even map makes that class nonzero, and
directness gives the contradiction. The positive offset values are
identified with their actual natural absolute values and rational
casts. Two disjoint equations supply the required distinct pair.
This includes horizontal slopes alpha=0; swapping the coordinates
also proves the vertical-line functional-square obstruction.

The result is connected to the actual split-radical coordinate
algebra. The literal polynomial map substituting a rational line
is checked on each scaled split radicand. Any ring homomorphism
from the actual coordinate tower to Q(T) agreeing with that line
map on Q[X,Y] would turn every actual radical-square relation into
the forbidden functional squares. Its nonexistence is proved, so
the obstruction is not left as an unexplained square-condition input.

This extends the one-sided arithmetic refinement P1-MATH-0019 to
selected sets and the line step of T1.7. Its earlier complete T20.5
validation is preserved in the finding history. No independence
weakening is claimed for the entire two-variable host-count lemma.
The geometric step identifying a curve of minimal projective degree
with a degree-one function-field map to a line remains open, as do
the weighted projective degree formulas, surface coverings and final
two-variable counts. T1.7 stays in_progress, coverage stays 79/167
and confirmed improvements stay 105. No external estimate, dependency
download, source-byte modification or Palomar registration is introduced.

Verified with Lean v4.36.0-rc2: full lake build (11401 jobs), actual Audit.lean kernel-axiom audit (7882 declarations; only propext, Classical.choice, Quot.sound), all 5599 ledger references, source integrity (138 manifest entries / 167 numbered results), and git diff --check. Ubuntu root free space: 14.37 GiB.


## The literal homogenized split-radical coordinate domain

The underlying coordinate algebra of the actual homogenized
split-radical presentation in Step 2 of companion T1.7 is now proved
to be a domain. Over every characteristic-zero field F, take the
literal polynomial ring F[Z][X][Y] and actual radicands
  c_i*Z^(e_i)*product_(a in I_i)(X+a*Z)*product_(b in J_i)(Y+b*Z).
The coefficients c_i are arbitrary nonzero elements, the integer
root lists are pairwise disjoint in each coordinate, and at least
one list in each equation is nonempty. The literal quadratic tower
is finite free of rank 2^k over this three-variable base. Its domain
property is proved internally for arbitrary natural e_i, and hence
includes the source exponents e_i=2D-|I_i|-|J_i|. No point-height
or coefficient-smoothness premise enters this algebraic assertion.

The proof first extends the nonsquare split-word lemmas from integer
roots to arbitrary finite sets of distinct field roots. These
supporting nonsquare and finite-product independence statements hold
over any field; the subsequent actual quadratic-field construction
uses characteristic zero as before. Nonempty disjoint selections
have nonsquare product, and their actual generic tower is proved
to be a field of degree 2^k. No Kummer or field-degree assertion
is assumed as an input.

For the homogenized system, an explicit injective coefficient map
F[Z]->F(Z) is lifted through both polynomial coordinates. If z is
the actual nonzero fraction-field image of Z, the source root lists
become the literal finite sets {a*z:a in I_i} and {b*z:b in J_i}.
Their disjointness is proved using the injectivity of a->a*z in
characteristic zero. The mapped coefficient is c_i*z^(e_i), proved
nonzero. Every actual radicand and the complete equation list are
proved to map to these exact scaled root words. Passing to the
fraction field F(Z)(X,Y) gives the internally constructed generic
field. The recursive tower base-change map is faithful, proving
that the original homogenized coordinate algebra is a domain.

This provides the literal integral algebra underlying the source
weighted presentation, including over an algebraically closed base.
The formal grading, the explicit Z=1 specialization, generation of
the D-th Veronese algebra, the projective embedding and cover-degree
and curve-degree identities remain open. The surface coverings and
two-variable host counts also remain open. T1.7 stays in_progress,
numbered coverage stays 79/167 and confirmed improvements stay 105.
These are checked source-algebra foundations with no new improvement
identifier. No external input, dependency download, original-source
change or Palomar registration is introduced.

Verified with Lean v4.36.0-rc2: full lake build (11409 jobs), actual Audit.lean kernel-axiom audit (7911 declarations; only propext, Classical.choice, Quot.sound), all 5628 ledger references, source integrity (138 manifest entries / 167 numbered results), and git diff --check. Ubuntu root free space: 14.36 GiB.


## The literal weighted presentation, homogeneous relations and Z=1 chart

The literal weighted polynomial quotient in Step 2 of T1.7 is
now identified with the already constructed homogenized radical
coordinate algebra. This is an explicit ring equivalence, rather
than an identification of informal presentations. The actual
quotient by W_i^2-c_i*Z^(2D-|I_i|-|J_i|)*product(X+aZ)*product(Y+bZ)
is consequently proved to be a domain over every characteristic-zero
field, under the source nonzero-coefficient, nonempty and disjoint
root-list hypotheses. No integrality premise is left in this source
corollary.

A general presentation theorem first constructs inverse algebra maps
between R[W_1,...,W_k]/(W_i^2-a_i) and the literal quadratic tower,
for every commutative ring R and every radicand list, including the
empty list. The maps preserve every radical generator. The kernel
of the actual polynomial evaluation is proved to be exactly the
relation ideal. The weighted presentation is transported to this
general quotient through the actual variable-sum equivalence and
the checked three-variable polynomial equivalence. Every generator
and every actual source relation is tracked through those maps.

In the native three-variable polynomial ring, the homogenized
radicands are proved homogeneous of degree 2D whenever their root
count is at most 2D. Nonzero coefficients give nonzero radicands and
exact total degree 2D; these polynomial statements hold over every
field, without a characteristic-zero assumption. The actual weighted
relations, with base-variable weights 1 and radical-variable weight
D, are proved weighted homogeneous of degree 2D. Their literal span
ideal is homogeneous for the native weighted polynomial grading.

The Z=1 coefficient evaluation, lifted through both polynomial
coordinates, sends each actual homogenized radicand and the entire
list to the previously checked affine system. The recursive base
change supplies an actual ring homomorphism between the corresponding
coordinate algebras, commuting with this base evaluation.

The induced quotient grading as a bundled graded algebra, generation
of its D-th Veronese algebra, the projective construction and its
cover- and curve-degree formulas remain open. This checkpoint does
not infer projective degree formulas from the affine polynomial
identities. The external surface covering and the two-variable host
counts also remain open. T1.7 stays in_progress, numbered coverage
stays 79/167, and confirmed improvements stay 105. These are checked
source-algebra foundations with no new improvement identifier. No
external estimate, new dependency, original manuscript change or
Palomar registration is introduced.

Verified with Lean v4.36.0-rc2: targeted builds and full lake build (11419 jobs), actual 7955-declaration axiom audit, all 5672 ledger/finding declaration references, 138 preserved source-manifest entries and the complete 167-result inventory. Only propext, Classical.choice and Quot.sound occur. Ubuntu root free space: 14.34 GiB. Numbered coverage remains 79/167; confirmed improvements remain 105.


## The actual quotient grading and precise Veronese generators

The literal weighted quotient in T1.7 Step 2 now carries a
constructed GradedAlgebra structure. Weighted homogeneous polynomial
components descend through the actual homogeneous relation ideal as
linear projections on the quotient. On each actual image piece,
projection to its own degree is the identity and projection to every
other degree is zero. These projections prove injectivity of the
canonical direct-sum recomposition; polynomial decomposition proves
surjectivity. Multiplication and the unit respect the actual pieces.
This is a proved quotient grading, not a grading asserted from the
notation. The general construction works over every commutative
coefficient ring and every homogeneous weighted polynomial ideal.

For the source quotient, the actual base variables have degree 1 and
the actual radical variables have degree D, with their literal
projection formulas checked. For positive D its degree-zero piece
is exactly the scalar image. The root-count bound at most 2D supplies
the previously proved homogeneity of the source relation ideal.

The D-th Veronese algebra is defined as the actual range of the
canonical algebra map from the direct sum of pieces of degrees nD.
Its underlying module is proved to be the supremum of these actual
pieces. It equals the subalgebra generated by those pieces, and is
now proved generated by the single piece of degree D. The argument
splits actual finitely supported exponent vectors of weights 1 or
D into successive vectors of weight D, proves the monomial image
statement and then sums homogeneous polynomials. It applies through
every algebra map, including the actual quotient map; no Veronese
generation assertion is supplied as an input.

The precise source generator set is also proved: the base monomials
of ordinary degree D with every radical exponent zero, together
with the individual radical variables. Every weight-D monomial with
a radical factor is proved to be that single radical times a scalar;
all remaining monomials are the stated pure base monomials. Their
images generate the actual source Veronese algebra. For finitely many
radicals the generator set is finite and the Veronese algebra is
proved of finite type. Under the actual characteristic-zero source
root-list hypotheses, its domain property is discharged internally
using the previous literal quotient-domain theorem.

This completes the source-algebra grading and Veronese-generation
steps. The projective construction, finiteness over the projective
plane, its cover degree and the surface- and curve-degree identities
remain open. No projective degree formula is inferred solely from
this algebraic generation result. The external surface covering and
the two-variable host counts remain open. T1.7 stays in_progress,
numbered coverage stays 79/167 and confirmed improvements stay 105.
No new improvement identifier, external estimate, dependency download,
original manuscript change or Palomar registration is introduced.

Verified with Lean v4.36.0-rc2: targeted builds and full lake build (11431 jobs), actual 7993-declaration axiom audit, all 5710 ledger/finding declaration references, 138 preserved source-manifest entries and the complete 167-result inventory. Only propext, Classical.choice and Quot.sound occur. Ubuntu root free space: 14.33 GiB. Numbered coverage remains 79/167; confirmed improvements remain 105.


## The finite inclusion over the pure base Veronese image

The actual inclusion of the pure base Veronese image into the
source Veronese algebra is now proved to be a finite ring map.
The base image is the subalgebra of the literal weighted quotient
generated by the images of the degree-D monomials in the three base
variables. The target is the actual Veronese algebra constructed as
the range of the direct sum of its multiple-degree pieces. The map
is the literal inclusion of these subalgebras.

Native homogeneous polynomials of every degree nD in the three base
variables are proved to map into that pure base algebra, using the
already checked exponent splitting and the explicit coefficient and
monomial maps. In particular every actual source homogenized
radicand, of degree 2D, belongs to the base image. This membership is
proved for the exact c_i*Z^(2D-|I_i|-|J_i|) split products, rather
than supplied as an abstract integrality premise.

Each actual quotient radical is packaged as an element of the target
Veronese algebra. Its square is proved equal to the actual radicand
image using membership of the literal defining relation in the
literal relation ideal. The target is proved to be generated by the
base image and these radicals. A general checked finite-inclusion
lemma constructs the canonical relative algebra, proves every such
radical integral by its monic quadratic relation, verifies that its
adjoin is the entire target and proves module finiteness. Applying
that lemma discharges every premise with the actual source objects.

This finite-map statement holds over every field, for finitely many
equations, positive D and root counts at most 2D. It needs no
nonzero-coefficient, characteristic-zero or disjointness hypothesis;
those separate hypotheses already prove integrality of the source
Veronese algebra. Finiteness here concerns the affine Veronese cone
inclusion. The identification of the pure base image with the
standard plane Veronese algebra, the relative free rank and cover
degree 2^k, the projective finite morphism and all projective degree
formulas remain open. The external surface covering and two-variable
host counts remain open. T1.7 stays in_progress, numbered coverage
stays 79/167 and confirmed improvements stay 105. No new improvement
identifier, external estimate, dependency download, original-source
change or Palomar registration is introduced.

Verified with Lean v4.36.0-rc2: targeted builds and full lake build (11437 jobs), actual 8004-declaration axiom audit, all 5721 ledger/finding declaration references, 138 preserved source-manifest entries and the complete 167-result inventory. Only propext, Classical.choice and Quot.sound occur. Ubuntu root free space: 14.32 GiB. Numbered coverage remains 79/167; confirmed improvements remain 105.


## The faithful finite map from the standard base Veronese algebra

The pure base algebra in T1.7 Step 2 is now identified by an
explicit F-algebra equivalence with the standard D-th Veronese
algebra of the native polynomial ring F[X,Y,Z]. This standard algebra
is defined as the actual range of the direct sum of the ordinary
homogeneous pieces of degrees nD, not as a polynomial ring assumed
to represent the base.

The coded pure base monomials in the full weighted variable set are
proved to be exactly the images, under the literal base-variable
rename, of ordinary degree-D monomials in three variables. The reverse
identification constructs the actual exponent preimage and proves
that its image is the original exponent vector using the vanishing
of all radical exponents. Native homogeneous degree-D polynomials
and the standard Veronese algebra have these exact generators.
Mapping them through the actual quotient gives precisely the pure
base image used in the finite-inclusion checkpoint.

The complete native three-variable polynomial map into the literal
weighted quotient is proved injective. Under the explicit weighted
presentation equivalence, its value on every polynomial is the
canonical base image of that polynomial under the checked
three-variable equivalence into the actual radical tower. The base
map into this tower is injective even for arbitrary radicands. Thus
the base injectivity uses no domain assertion and no square-class
independence premise. Restriction to the standard Veronese algebra
gives the stated explicit base equivalence and its value formula.

Composing this equivalence with the already verified pure-base
inclusion constructs the actual standard-base-to-source-Veronese
ring map. Its injectivity and finiteness are proved. These results
hold over every field for the exact indexed source system; positive
D and the source root-count bound supply the finite-map assertion.
No nonzero-coefficient, characteristic-zero or disjointness premise
is needed for this finite faithful base map. The separate source
integrality theorem retains its own exact hypotheses.

The relative free rank and generic cover degree 2^k, the projective
finite morphism, the identification of the base projective scheme
with the projective plane, and all projective degree formulas remain
open. This checkpoint identifies and proves the actual affine-cone
base map; it does not infer those projective conclusions from ring
finiteness alone. The external surface covering and two-variable
host counts remain open. T1.7 stays in_progress, numbered coverage
stays 79/167 and confirmed improvements stay 105. No new improvement
identifier, external estimate, dependency download, original-source
change or Palomar registration is introduced.

Verified with Lean v4.36.0-rc2: targeted builds and full lake build (11441 jobs), actual 8015-declaration axiom audit, all 5732 ledger/finding declaration references, 138 preserved source-manifest entries and the complete 167-result inventory. Only propext, Classical.choice and Quot.sound occur. Ubuntu root free space: 14.31 GiB. Numbered coverage remains 79/167; confirmed improvements remain 105.


## P1-MATH-0106 — An actual relative free basis of the source Veronese algebra

The actual source D-th Veronese algebra is now proved finite
free of rank 2^k over the standard three-variable D-th Veronese
base. A literal basis is constructed and its value in the weighted
quotient is checked on every basis index. This strengthens the
finite-base-map result and is recorded as P1-MATH-0106. It concerns
the source Veronese algebra; P1-MATH-0105 concerns the different
radical-sum affine image algebra.

Each actual homogenized radicand has ordinary degree 2D and is
constructed as an element of the standard Veronese base. The literal
quadratic tower over that base is free of rank 2^k by its recursive
normal basis. Its coefficient inclusion into the full three-variable
polynomial ring is proved injective, and each actual radicand and
the complete equation list are proved to map to their exact original
homogenized polynomials. The faithful tower base change is followed
by literal list transport and the explicit weighted presentation
equivalence, giving an actual injective map into the source quotient.

Every radical generator, every normal basis vector and the base
inclusion are proved to commute with the actual base change. The
relative map sends its generators to the exact source quotient
radicals, with all list indices tracked. Its image as a base algebra,
after restricting scalars, is proved to be exactly the source
Veronese algebra: the scalar range is the previously identified pure
base image and the generator range is the actual radical range.
The exact source generation theorem supplies both inclusions.

The image basis is transported through this proved image equality
to the actual source Veronese algebra. Its module structure is the
one induced by the previously constructed standard-base ring map,
and the scalar compatibility is checked explicitly. The resulting
basis, freeness, module finiteness and exact rank 2^k are internal
Lean conclusions. No freeness, image equality, degree or counting
assertion is supplied as an assumption.

The finite-free statement holds over every field and for arbitrary
coefficients, including zero coefficients, whenever D is positive
and every root count is at most 2D. It does not require characteristic
zero, disjointness, nonempty root sets or generic square-class
independence. Those hypotheses remain separate inputs to the already
proved integrality statement. The general basis and faithful-map
lemmas work for arbitrary commutative coefficient rings, with
nontriviality where needed for finrank.

This supplies the exact relative algebraic free rank underlying
Step 2. The projective construction, the base projective-scheme
identification, the degree-zero function-field bridge, the projective
cover degree and all surface- and curve-degree formulas remain open.
No projective conclusion is inferred solely from this affine-cone
module computation. External surface coverings and two-variable
host counts remain open. T1.7 stays in_progress and numbered coverage
stays 79/167. Confirmed improvements total 106; no manuscript
conclusion error is asserted. No external estimate, dependency
download, original-source change or Palomar registration is introduced.

Verified with Lean v4.36.0-rc2: targeted builds and full lake build (11455 jobs), actual 8044-declaration axiom audit, all 5761 ledger/finding declaration references, 138 preserved source-manifest entries and the complete 167-result inventory. Only propext, Classical.choice and Quot.sound occur. Ubuntu root free space: 14.29 GiB. Numbered coverage remains 79/167; confirmed improvements total 106.


## P1-MATH-0106 extended — The actual rescaled grading, homogeneous basis and graded base map

Both actual Veronese algebras now carry the grading in which
original degree nD becomes degree n. The construction is made on
their literal direct-sum range algebras, with degree-n piece equal
to the preimage of the original degree-nD piece. Original homogeneous
projections lift to actual linear projections on the Veronese
algebra. For positive D their action on each image piece is the
identity in its own degree and zero in every other degree.
Injectivity and surjectivity of recomposition are proved, followed
by the actual GradedAlgebra structure and its projection formula.

For the standard three-variable base and the literal source weighted
quotient, generation in degree D is transported to generation of
these actual rescaled rings by their degree-one pieces. Every exact
source generator, including each radical, is proved to belong to
degree one. The source degree-zero piece is exactly its scalar image.
The source quotient grading uses the source root-count bound; the
rescaling uses positive D. No generation or decomposition assertion
is assumed as an unproved interface.

The free normal basis of P1-MATH-0106 is now proved homogeneous. A
recursive index weight counts the selected radicals and is proved
at most k. For any actual ring map from a quadratic tower to a
graded ring, homogeneous radical images of degree D imply that the
image of each literal normal basis vector has degree D times its
index weight. Applying this statement to the exact relative map,
using its checked generator formulas, proves that the actual source
basis vector belongs to rescaled degree equal to that weight, with
all weights between 0 and k. This is a statement about the already
constructed source basis, not a new basis assumed homogeneous.

Finally the actual finite faithful standard-base map is proved to
preserve every rescaled degree and is bundled as a GradedRingHom.
The proof transports every ordinary homogeneous native base
polynomial through the literal variable rename into the weighted
polynomial grading, and then through the actual quotient map. The
bundled graded map retains the previously verified injectivity and
finiteness properties. These results extend P1-MATH-0106 without a
new improvement identifier.

The Hilbert-function computation, projective construction and its
degree-zero function-field bridge, finite projective cover degree
and all surface- and curve-degree identities remain open. The
external surface covering and two-variable host counts remain open.
T1.7 stays in_progress, numbered coverage stays 79/167 and confirmed
improvements stay 106. No external estimate, dependency download,
original-source change or Palomar registration is introduced.

Verified with Lean v4.36.0-rc2: targeted builds and full lake build (11469 jobs), actual 8070-declaration axiom audit, all 5787 ledger/finding declaration references, 138 preserved source-manifest entries and the complete 167-result inventory. Only propext, Classical.choice and Quot.sound occur. Ubuntu root free space: 14.28 GiB. Numbered coverage remains 79/167; confirmed improvements remain 106.


## Actual projective scheme map

The actual rescaled standard-base inclusion now induces a constructed
morphism of schemes from the source Proj to the native standard
Veronese Proj. Its inverse image of every base basic open D(b) is
exactly the source basic open D(f(b)). This construction uses the
literal graded inclusion and the actual source quotient, rather
than an assumed projective model.

The admissibility criterion is proved: the source irrelevant ideal
is contained in the radical of the mapped base irrelevant ideal.
The source generators are proved to generate their actual ring;
the irrelevant ideal of a ring generated in degree one is proved
to be their ideal span. Each pure base generator lies in the mapped
base irrelevant ideal, while the square of each radical generator
lies there by its actual homogeneous radicand relation. These
arguments apply over every field, including zero radicand
coefficients, for positive D and root counts at most 2D.

The pinned Mathlib Proj functor takes the stronger condition
H_plus <= map(G_plus). The quadratic source supplies the sufficient
radical containment above. A local extension implements the point
map, its continuity, the structure-sheaf map and its locality on
stalks under that weaker condition, and bundles the resulting
Scheme.Hom. This is a library interface extension, not an error
in the manuscript or a new mathematical-change identifier.

Finiteness of the scheme morphism, identification of the base Proj
with the projective plane, the degree-zero function-field bridge,
the degree 2^k of the projective cover, surface degree 2^k D^2,
curve-degree identities and the external surface covering and
host counts remain open. T1.7 stays in_progress, numbered coverage
stays 79/167 and confirmed mathematical improvements stay 106.
No original manuscript source is changed. Palomar remains deferred.

See [statement alignment and upstream provenance](PROJECTIVE_MAP_ALIGNMENT.md).

Verified with Lean v4.36.0-rc2: full build 11821 jobs, direct axiom audit of 8089 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 5799 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 13.95 GiB.


## P1-MATH-0106 extended — Finiteness of the actual projective morphism

The constructed projective source morphism is now proved finite
as a morphism of schemes. This is the literal map from the source
Veronese Proj to the standard native Veronese Proj, not merely the
already verified finite map of affine cones. The theorem applies
over every field for arbitrary coefficients, positive D and root
counts at most 2D. Characteristic zero and root independence are
not required for finiteness.

For any nonnegatively graded commutative ring and any homogeneous
element b of degree one, a ring homomorphism to its degree-zero
homogeneous localization is constructed by sending each degree-n
component a to a/b^n. Compatibility with addition, multiplication
and one is proved, followed by its formula on homogeneous
elements, surjectivity and naturality for actual graded ring maps.
Surjectivity and naturality transport a finite total ring map to
a finite map of these actual chart rings, including degenerate
charts, without a nonzero or domain assumption.

The radical-admissible projective morphism is proved to restrict on
each degree-one basic open to the corresponding Spec map, under
the actual chart isomorphisms. Finiteness of that ring map proves
finiteness of each restricted scheme map. Degree-one base opens
cover the entire target by the proved irrelevant-ideal span
identity and generation in degree one. Zariski locality then
proves finiteness of the actual global projective morphism.

This extends the argument supporting P1-MATH-0106; no new
mathematical-change identifier is introduced. The cover's generic
degree, identification of the base Proj with the projective plane,
the degree-zero function-field bridge, the Hilbert calculation,
surface degree 2^k D^2, curve-degree identities and external host
counts remain open. T1.7 stays in_progress, coverage stays 79/167,
confirmed improvements stay 106 and Palomar remains deferred.

Verified with Lean v4.36.0-rc2: full build 12009 jobs, direct axiom audit of 8103 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 5813 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 13.78 GiB.


## P1-MATH-0106 extended — The actual finite flat cover has constant rank 2^k

The actual projective source morphism is now proved finite,
flat, surjective and of constant scheme rank 2^k. The rank statement
is the equality of Mathlib's Scheme.Hom.finrank with 2^k at every
point of the actual native Veronese Proj. It applies over every
field, to arbitrary coefficients including zero, for positive D
and source root counts at most 2D. In particular the geometric
flatness and constant-rank assertions do not require generic
square-class independence or characteristic zero.

The degree-one dehomogenization map has proved kernel generated
by b-1, and gives an actual ring equivalence from that quotient to
the homogeneous localization. The proof constructs the inverse
evaluation using the ordinary localization, where b maps to one.
A literal ring basis is transported to the quotient by tensor
base change, then through the constructed ring equivalences and
coefficient transport. This proves that a free graded ring map
has an actual free map on each degree-one chart, with basis the
dehomogenized original basis. Homogeneity of the original basis
is used for the explicit fraction formula, not assumed for the
base-change basis argument itself.

For the source, the exact chart basis vector is the previously
constructed normal basis vector divided by f(b) to its explicit
radical-count weight. Every nonzero native chart is a domain and
the actual source chart module is finite free of rank 2^k. The
base and source actions are the actual homogeneous-localization
map, not auxiliary actions assumed compatible.

The actual projective map is flat by those chart bases and Zariski
locality. Each chart square is proved to be a pullback. Mathlib's
finite-flat scheme rank is then computed on that pullback from
the literal chart basis. The proved degree-one target cover gives
constant rank everywhere, and its positive value proves
surjectivity. This establishes the projective cover rank, not
only the rank of its affine cone.

This extends P1-MATH-0106 without a new identifier. The geometric
base is still the actual standard Veronese Proj; its explicit
identification with the projective plane remains open. The
degree-zero function-field bridge and its identification with
the manuscript's generic field, Hilbert computation, surface
degree 2^k D^2, curve-degree identities and external host counts
remain open. The constant scheme rank does not replace those
separate alignment steps. T1.7 stays in_progress, numbered
coverage stays 79/167, confirmed improvements stay 106 and
Palomar remains deferred.

Verified with Lean v4.36.0-rc2: full build 12061 jobs, direct axiom audit of 8129 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 5839 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 13.71 GiB.


## Actual integral projective schemes and their function fields

The actual native base and the actual source projective schemes
are now proved integral under the source integrality hypotheses.
The base needs only a field and positive D. The source retains
characteristic zero, nonzero radicand coefficients, at least one
root in each equation and the exact pairwise disjoint root-set
hypotheses already used for its coordinate-domain proof. The
positive degree and root-count bounds supply its rescaled grading.
No domain or integrality assertion is assumed as a new interface.

For a graded domain, homogeneous localization at any submonoid
avoiding zero is proved a domain by its faithful embedding into
the ordinary localization. Every actual Proj stalk is consequently
a domain, and the scheme is reduced. If the irrelevant ideal is
nonzero, the literal zero homogeneous prime is constructed as a
point and proved generic. This proves irreducibility, nonemptiness
and integrality, and identifies the scheme's chosen generic point
with that zero prime.

The native coordinate powers X_j^D are constructed in the actual
standard Veronese algebra, with proved degree-one membership and
nonvanishing. The Z^D coordinate proves nonzero irrelevant ideals
for both the base and, by the faithful graded base inclusion, the
source. These facts discharge the nonempty-Proj hypotheses on the
literal algebras used for the projective cover.

The actual scheme function field is constructed as ring-equivalent
to the homogeneous localization at the zero ideal: fractions of
homogeneous numerators and nonzero denominators of the same degree.
The latter ring is proved a field. A faithful radical-admissible
graded map is proved to map the zero prime and generic point to
their actual counterparts. Its map of scheme function fields is
constructed directly from the scheme morphism's stalk map and
proved injective. The corresponding map on degree-zero homogeneous
fractions is also constructed. These constructions are instantiated
for the exact projective base inclusion of the source, retaining
all the stated source hypotheses.

The remaining alignment includes the compatibility of the two
function-field maps under these equivalences and identification
with the affine split-radical generic field in the manuscript.
The degree of that actual field extension is not yet certified by
the already proved constant scheme rank. The explicit base Proj
identification with the projective plane, Hilbert computation,
surface degree 2^k D^2, curve-degree identities and external host
counts remain open. T1.7 stays in_progress, coverage stays 79/167,
confirmed improvements stay 106 and Palomar remains deferred.

Verified with Lean v4.36.0-rc2: full build 12075 jobs, direct axiom audit of 8151 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 5867 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 13.69 GiB.


## Naturality of the actual projective function-field map

The map on actual scheme function fields is now proved compatible
with the map on actual degree-zero homogeneous fractions. The
function-field equivalences and the generic-point stalk map are
exposed as their categorical isomorphism and morphism, preserving
their previous ring types and constructions. Their commuting
diagram is a proved equality of actual ring homomorphisms.

The proof transports a scheme stalk map along proved equalities
of source and target points. A Proj stalk compatibility theorem
identifies it with the actual homogeneous local ring map after
that point transport. At the zero homogeneous primes, this is
exactly the degree-zero fraction map of the original graded ring
homomorphism. Applying the checked generic-point equalities gives
the categorical square and then the ring-homomorphism square.

For the paper's source, the separately constructed map induced by
the actual projective morphism is proved equal to the general
construction. The literal base and source function-field
equivalences then give the commuting diagram with the actual
graded base inclusion on homogeneous fractions. All source domain
and integrality hypotheses remain explicit and are discharged by
the previously proved source domain and nonempty-Proj results.

Thus the naturality part of the degree-zero function-field bridge
is complete. Identification with the manuscript's affine
split-radical generic tower and the numerical degree of this
actual field extension remain open. The explicit plane
identification, Hilbert computation, surface degree 2^k D^2,
curve-degree identities and external host counts also remain
open. T1.7 stays in_progress, coverage stays 79/167, confirmed
improvements stay 106 and Palomar remains deferred.

Verified with Lean v4.36.0-rc2: full build 12079 jobs, direct axiom audit of 8157 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 5876 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 13.68 GiB.


## The actual projective function-field extension has degree 2^k

The actual extension of projective scheme function fields is now
proved finite of degree 2^k. Its algebra structure is the actual
stalk-induced map of the constructed source projective morphism.
By the previously proved naturality diagram, the actual map of
degree-zero homogeneous fraction fields has the same degree 2^k.
This computes the numerical field degree, separately from the
already proved constant finite-flat scheme rank.

For a nonzero degree-one homogeneous element b, its basic open
is proved nonempty by the actual zero homogeneous prime. The
chart map to the scheme function field is constructed by the
canonical localization-to-sections map followed by the actual
germ at the generic point. The scheme function field is proved
to be the fraction field of that chart ring, by its existing
affine-open fraction-field theorem and the actual chart section
isomorphism. No abstract field identification is assumed.

Naturality of these chart maps is proved first for germs and the
generic-point stalk map and then for the actual homogeneous
localization maps. This supplies both scalar-tower identities.
The fraction-ring dimension theorem equates the actual
function-field degree with the rank of the actual chart module.
The literal free chart basis therefore computes that field degree.

For the paper's source, the chart is the nonzero native Z^D
coordinate. The source chart basis and its index-cardinality
formula discharge the rank calculation as 2^k. The actual
geometric field extension is explicitly proved module-finite.
The checked ring equivalences and commuting diagram transport
the numerical degree to the actual homogeneous fraction-field
map. All source integrality hypotheses remain explicit:
characteristic zero, nonzero coefficients, nonempty root data,
pairwise disjoint root sets, the literal homogenized radicand
identities, positive D and the root-count degree bound.

Identification of these fields with the manuscript's explicit
affine split-radical generic tower remains open. The base target
is still the native standard Veronese Proj; its explicit plane
identification, the Hilbert/intersection calculation of surface
degree 2^k D^2, curve-degree identities and external host counts
remain open. T1.7 stays in_progress, numbered coverage stays
79/167, confirmed improvements stay 106 and Palomar remains
deferred. Original manuscript sources are unchanged.

Verified with Lean v4.36.0-rc2: full build 12087 jobs, direct axiom audit of 8167 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 5888 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 13.67 GiB.


## P1-MATH-0107 — Exact Hilbert function, polynomial and multiplicity of the actual source

The actual source homogeneous pieces now have explicit coefficient-field
bases and exact dimensions. If e ranges over the literal quadratic
normal-basis indices, and |e| is its proved radical-count weight, then

    h_S(n) = sum_{|e| <= n} binom(D(n-|e|)+2,2).

Every homogeneous piece is finite dimensional. For n >= k all normal
indices occur. The rational polynomial

    P_S(T) = (1/2) sum_e (DT-D|e|+1)(DT-D|e|+2)

is proved to equal these actual dimensions for every n >= k. Its
quadratic coefficient is 2^k D^2/2; for positive D its degree is exactly
two and its Hilbert multiplicity is 2^k D^2. This last invariant is
constructed from the unique eventual polynomial of the actual graded
pieces, not supplied as a premise or defined to be the target value.

The proof first restricts actual homogeneous vector bases to components.
The native standard Veronese basis consists of literal monomials.
The scalar-preserving literal base inclusion then composes that vector
basis with the actual relative free quadratic basis. Its component
indices are explicitly reindexed by radical weight and polynomial
exponents. Exponents of degree m are identified with symmetric powers,
giving the proved monomial count binom(m+2,2). The native base pieces
accordingly have dimension binom(nD+2,2).

All these dimension and Hilbert identities hold over any coefficient
field, including positive characteristic and zero radicand coefficients,
under the literal radicand identities, positive D and degree bound.
The separate characteristic-zero, nonzero-coefficient and root-disjointness
hypotheses remain necessary in the existing source-integrality argument.
This gives an elementary Hilbert-function proof of the numerical surface
factor appearing in Step 2, and a stronger exact formula for a revision.

The invariant computed here is the Hilbert multiplicity of the actual
chosen graded presentation. A scheme-theoretic comparison with the
manuscript's explicit projective embedding and hyperplane bundle, the
native target's identification with the plane, the curve-degree
projection formula and the external surface/curve host counts remain
open. The explicit affine generic-tower identification is also still
open. T1.7 remains in_progress and numbered coverage remains 79/167.
Confirmed mathematical improvements now total 107; no manuscript
conclusion error has been confirmed. Palomar remains deferred.
Original manuscript sources are unchanged.

Verified with Lean v4.36.0-rc2: full build 12115 jobs, direct axiom audit of 8213 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 5949 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 13.64 GiB.


## Actual projective charts and function fields match the literal affine system

The actual native and source Z-charts are now identified with the
literal affine rings in the manuscript. The native chart is the
polynomial plane F[X][X]. The source chart is the actual iterated
quadratic algebra with radicands c_i prod(X+a) prod(Y+b), indexed by
the original finite list. Scheme isomorphisms identify the actual
basic-open subschemes with the spectra of these rings.

The construction first proves, for any graded commutative coefficient
algebra and positive D, that its rescaled Veronese chart at b^D is
isomorphic to the original homogeneous chart at b. The literal map
uses dehomogenization and the quotient by b^D-1; its injectivity and
surjectivity are proved by clearing powers of b. No domain hypothesis
is used, and rings with zero divisors are included.

For the quadratic tower, coefficient specialization is proved
surjective when the base specialization is surjective, with kernel
exactly the extended base kernel. Specializing the homogenizing
variable to one has exactly the principal kernel (Z-1), both in the
coefficient ring and in the actual source coordinate quotient.
This produces the affine chart isomorphism without assuming a
geometric identification. The actual base variables and radical
generators are proved to map to their literal affine counterparts.
These ring and chart computations allow any coefficient field and
zero coefficients, under the explicit radicand identities and degree
bound used to construct the grading.

Under the separate existing source-integrality hypotheses, the
canonical scheme function fields are now explicitly isomorphic to
F(X,Y) and the affine generic split-radical tower. The proof uses the
canonical chart-to-generic-stalk map and its actual fraction-field
property, together with the previously verified affine generic tower
fraction-field theorem. The actual projective function-field map
commutes with these two explicit isomorphisms and the literal base
field inclusion. Naturality is proved on dehomogenized chart elements
and extended to the full fields by the localization universal property.
This closes the previously open affine generic-tower identification.

The native target's global projective-plane identification, the
comparison of the chosen graded presentation with the explicit
projective embedding and hyperplane bundle, the curve-degree
projection formula and the external surface/curve host counts remain
open. The source Hilbert multiplicity 2^k D^2, finite-flat rank 2^k
and actual function-field degree 2^k remain previously checked facts.
T1.7 remains in_progress, numbered coverage remains 79/167, confirmed
improvements remain 107 and Palomar remains deferred. Original
manuscript sources are unchanged.

Verified with Lean v4.36.0-rc2: full build 12143 jobs, direct axiom audit of 8258 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6010 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 13.60 GiB.


## Global standard projective-plane target and finite flat source projection

The native standard Veronese projective target is now globally
isomorphic to the standard projective plane, defined as Proj of the
ordinary homogeneous grading on F[X_0,X_1,X_2]. This is an actual
scheme isomorphism, constructed from the literal Veronese inclusion.
Composing it with the existing source morphism gives the actual
projection to that plane. This projection is proved finite, flat,
surjective and of constant scheme rank 2^k at every plane point.
These cover statements allow arbitrary coefficient fields and zero
radicand coefficients; the separate source-integrality hypotheses
remain explicit for function-field assertions.

The underlying general theorem proves Proj invariance under every
positive Veronese construction on an internally graded commutative
coefficient algebra. No domain, reducedness, characteristic-zero,
Noetherian or generation-in-degree-one hypothesis is used. The
inclusion multiplies the grading by D, so it is handled by a verified
positive-degree-scaling Proj functor, not incorrectly treated as a
same-degree graded homomorphism. Homogeneous ideal pullback is
justified by a proved projection identity; actual homogeneous
localization and local-ring maps multiply fraction degrees by D.

For admissibility, a positive-degree homogeneous element has its Dth
power in the positive part of the actual Veronese. The necessary
irrelevant-ideal containment therefore holds in the radical. On
every positive homogeneous chart the actual ring map is proved
bijective: all relevant numerator degrees are already multiples
of D. Local scheme chart compatibility and locality of being an
isomorphism then prove the global isomorphism. The point map,
structure sheaf maps and generic local-ring locality are constructed
and checked, rather than supplied as an abstract isomorphism premise.

The scaled-localization and Proj chart constructions adapt the
pinned Mathlib source with its Kenny Lau copyright and Apache 2.0
attribution preserved in the new modules. The upstream files and
pinned dependency are unchanged.

This closes the previously open global projective-plane target
identification. The numerical Hilbert multiplicity 2^k D^2, explicit
affine generic-field identifications and actual function-field
degree 2^k remain checked. Comparison with the chosen projective
embedding and hyperplane bundle, the curve-degree projection
formula, low-degree curve geometry and external surface/curve
point counts remain open. T1.7 remains in_progress, numbered
coverage remains 79/167, confirmed improvements remain 107 and
Palomar remains deferred. Original manuscript sources are unchanged.

Verified with Lean v4.36.0-rc2: full build 12159 jobs, direct axiom audit of 8285 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6049 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 13.58 GiB.


## Actual closed projective embedding, coordinate quotient and Hilbert degree

The actual source now has the closed projective immersion defined
by precisely its degree-D base monomials and radical coordinates.
The ambient scheme is the standard Proj of the ordinary polynomial
ring on that literal coordinate index. An explicit bijection
identifies the index with the disjoint union of ternary degree-D
exponents and the original radical indices. Its cardinality is
binom(D+2,2)+k, giving the manuscript ambient coordinate count.

The polynomial evaluation map to the actual source Veronese is
constructed, proved surjective and proved to preserve every
homogeneous degree. Its irrelevant-ideal admissibility follows
from the actual degree-one generators. Surjectivity descends to
all degree-one affine chart maps by dehomogenization. Their actual
spectrum maps are closed immersions, and the checked chart
compatibility proves the global source map is a closed immersion.
No closed-immersion premise is supplied as an external input.

The homogeneous coordinate ideal is exactly the kernel of that
same polynomial evaluation map. It is proved homogeneous. Its
literal polynomial quotient has the grading whose pieces are the
images of the ordinary homogeneous polynomial pieces. The actual
quotient algebra is proved isomorphic to the source Veronese, and
every graded piece is identified by a linear equivalence.
Thus the coordinate quotient and grading used in the Hilbert
calculation match the verified chosen projective presentation.

Every coordinate piece is finite dimensional. The previously
computed exact source Hilbert function and unique eventual
quadratic polynomial are transported to these actual coordinate
pieces. Their Hilbert multiplicity is proved to be 2^k D^2.
The closed immersion and this numerical multiplicity are bundled
in one checked statement. This computes the Hilbert degree in the
manuscript's explicit projective coordinates, rather than only an
invariant of an unidentified graded algebra.

The structural embedding permits arbitrary coefficient fields and
zero coefficients under the explicit degree bound and positive D.
The Hilbert formula retains the literal original radicand identities.
The separate source-integrality hypotheses are unchanged for
function-field arguments. The hyperplane-bundle pullback comparison,
curve-degree projection formula, low-degree curve geometry, a
scheme-dimension comparison and external surface/curve point counts
remain open. T1.7 stays in_progress, numbered coverage remains
79/167, confirmed improvements remain 107 and Palomar remains
deferred. Original manuscript sources are unchanged.

Verified with Lean v4.36.0-rc2: full build 12173 jobs, direct axiom audit of 8318 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6098 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 13.56 GiB.


## Plane-equation quotient and actual Veronese Hilbert degree

For the literal quotient F[X,Y,Z]/(f), with nonzero homogeneous f
of degree e, multiplication by f is an injective map from the
ordinary degree-n piece to the degree-(n+e) piece. Its actual range
is exactly the kernel of the homogeneous quotient map. Rank-nullity
and the proved monomial bases therefore give
h(n+e)+binom(n+2,2)=binom(n+e+2,2).
Every quotient piece is finite dimensional. Its unique eventual
Hilbert polynomial is eT+(3e-e^2)/2. For positive e its degree is
one and its Hilbert multiplicity is e.

For any internally graded algebra over a field, the actual rescaled
D-th Veronese piece is proved linearly equivalent to the original
degree-nD piece. For positive D, any established Hilbert polynomial
P becomes P(DT); its multiplicity is multiplied by D^(deg P).
These are proved from the actual pieces and polynomial composition.
Applying this to the literal plane-equation quotient gives Hilbert
degree De for its D-th Veronese, with its quotient and Veronese
gradings explicitly constructed.

These calculations hold over any coefficient field. The plane
Hilbert identities require neither irreducibility nor reducedness
of f, only f nonzero and homogeneous; positivity of e and D is
explicit when claiming degree one or Veronese rescaling. No general
Hilbert-polynomial existence theorem is assumed.

This proves the target plane-curve factor De needed in Step 2.
The remaining comparison with the Hilbert degree of an arbitrary
integral curve in the actual source still requires the finite
graded-module rank formula and its degree-zero field comparison.
The full curve projection-degree formula, scheme-dimension and
hyperplane-bundle comparisons, low-degree curve geometry and
external host-count inputs remain open. T1.7 stays in_progress,
numbered coverage remains 79/167 and confirmed improvements remain
107. Palomar remains deferred; original sources are unchanged.

Verified with Lean v4.36.0-rc2: full build 12185 jobs, direct axiom audit of 8351 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6144 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 13.55 GiB.


## Actual graded curve quotients, finite module rank and Hilbert comparison

The finite graded-module comparison is now constructed from actual
homogeneous generators. The component map sends a tuple of coefficients
in degrees n-w_i to the actual sum of their images times the generators.
Projection onto homogeneous components proves surjectivity for a
generating family; actual module independence proves injectivity.
Both dimension inequalities follow from checked linear maps.

A maximal independent subfamily of finite generators is selected using
the pinned Mathlib theorem, with a common nonzero module denominator.
A nonzero homogeneous component of that denominator gives an injection
from each sufficiently high target piece into the range of a shifted
free component map. The reverse injection comes from independence.
Thus the actual target Hilbert function is squeezed between the sums
of the source functions at n-w_i and n+m-w_i. The subfamily cardinality
is proved equal to the actual module finrank, and also to the rank of
compatible fraction-field extensions, rather than supplied as a premise.

If the base function is eventually an+b, the target function differs
from rank*a*n by a bounded rational error. This numerical slope is
proved unique. Any polynomial eventually equal to a function with
that bounded error must be affine: a nonconstant remaining polynomial
would have unbounded absolute evaluations on natural arguments.
Consequently, if a target Hilbert polynomial exists and a is positive,
its degree is proved to be one and its Hilbert multiplicity equals
rank*a. Neither the polynomial degree nor the multiplicity identity
is assumed. General existence of the target polynomial remains an
explicit ordinary theorem argument, with no new axiom.

The actual quotient by any homogeneous ideal is supplied with its
image grading, decomposition, projection maps and graded quotient map.
An actual graded algebra map descends to the quotient by a target
ideal and its actual preimage. The descended map is injective, and
the given finite homogeneous module generators descend literally.

These constructions are instantiated for homogeneous prime quotients
of the manuscript source Veronese, using its actual quadratic normal
basis and radical-count weights. The source quotient and its base
preimage quotient are domains, their actual pieces are finite
dimensional, and their module rank is between 1 and 2^k. Their Hilbert
slope and, when the explicitly required polynomial exists, their
multiplicity obey the proved rank formula for any established affine
base Hilbert polynomial. The actual quotient maps, gradings and
generator identities are included in the checked statements.

The full manuscript curve projection formula is still open. The
remaining bridges include general Hilbert-polynomial existence for
these curve quotients, identification of the image with its literal
plane-equation Veronese, and comparison of cone-module rank with the
degree-zero projective function-field extension. Scheme dimension,
hyperplane-bundle comparison, low-degree curve geometry and external
host-count inputs also remain open. T1.7 stays in_progress; numbered
coverage remains 79/167, confirmed improvements remain 107 and Palomar
remains deferred. Original manuscript sources are unchanged.

Verified with Lean v4.36.0-rc2: full build 12203 jobs, direct axiom audit of 8413 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6229 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 13.53 GiB.


## Actual projective curve quotient function-field rank

The finite graded-module rank is now identified with the degree of
the actual projective function-field map. This comparison is proved
through literal degree-one affine charts, with no Laurent-polynomial
identification or cone-field degree supplied as a premise.

The common denominator of an independent homogeneous free approximation
can be chosen homogeneous and nonzero. Every component of an arbitrary
clearing denominator still clears the entire module: the proof handles
both the allowed-degree terms and the terms below a generator weight,
then recomposes an arbitrary element from its homogeneous components.

For a nonzero degree-one chart coordinate, dehomogenization is injective
on each homogeneous component of a domain. Every chart element has
representatives in all sufficiently large degrees. For a finite family
of chart coefficients, their representative degrees can be adjusted
simultaneously against the actual generator weights. Thus a relation
between the dehomogenized independent generators lifts to a single
homogeneous relation in the original module, proving chart independence.
Actual finite generators and the homogeneous denominator descend by
the checked dehomogenization diagram. The same independent subfamily
therefore computes both the global module rank and the chart-module
rank. Their equality is proved, rather than assumed.

The actual generic-point function fields are already proved to be the
fraction fields of these charts. Their checked naturality and the
pinned fraction-field rank theorem identify the degree of the actual
scheme function-field map with the chart rank, hence with the global
finite graded-module rank.

Irrelevant ideals commute with surjective graded maps. The actual
irrelevant-ideal radical bound is proved to descend to a homogeneous
target quotient and its actual base preimage quotient. This constructs
the projective morphism between the literal source prime quotient and
its literal base quotient. A nonzero degree-one base coordinate proves
both projective spectra nonempty and integral. Their actual geometric
function-field map is constructed and its degree is proved equal to
the already computed source-quotient module rank, between 1 and 2^k.
The source Hilbert multiplicity comparison is restated using this
actual projective field degree, still with the target Hilbert-polynomial
existence and the actual affine base polynomial as explicit arguments.

This closes the module-to-projective-function-field rank comparison
for these actual quotients. The full manuscript curve formula still
requires general Hilbert-polynomial existence for the curve quotients
and identification of the base image quotient with the literal
plane-equation Veronese, whose Hilbert degree De is already checked.
Scheme dimension, hyperplane-bundle comparison, low-degree curve
geometry and external host-count inputs remain open. T1.7 stays
in_progress; numbered coverage remains 79/167, confirmed improvements
remain 107 and Palomar remains deferred. Original sources are unchanged.

Verified with Lean v4.36.0-rc2: full build 12221 jobs, direct axiom audit of 8440 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6261 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 13.50 GiB.


## Hilbert-polynomial existence from two actual parameters

Hilbert-polynomial existence is now proved for an internally graded
F-algebra domain finite over two actual degree-one parameters, with
finite-dimensional homogeneous pieces. Finite module generation, rather
than a Hilbert-polynomial existence premise, is the input.

A homogeneous polynomial in one variable is its actual coefficient
times the corresponding monomial. After the degrees of finitely many
homogeneous generators, multiplication by that parameter is surjective
on consecutive module pieces. Their finite dimensions decrease and
therefore eventually stabilize. This proves an actual constant Hilbert
polynomial for any such one-parameter module, including rings with
zero divisors.

For two parameters, the actual homogeneous quotient by the first
parameter is generated over the second. The polynomial coefficient
map that kills the first variable is constructed and checked. The
quotient Hilbert function therefore stabilizes. If the first parameter
is nonzero in the domain, the checked hyperplane exact sequence gives
an affine Hilbert function by a natural-number recurrence. If it is
zero, the original Hilbert function is already eventually constant.
Both cases produce actual rational Hilbert polynomials. Finally, finite
module generation yields a finite homogeneous generating family by
taking the finitely many components of actual finite generators.

The theorem still needs a checked two-parameter finite normalization
for the actual curve quotients. Identification of the base image
quotient with the literal plane-equation Veronese remains open, as do
scheme dimension, hyperplane-bundle comparison, low-degree geometry
and external host-count inputs. No manuscript result is counted as
complete on the basis of this general algebraic step. Coverage stays
79/167 and the confirmed mathematical-improvement count stays 107.
Palomar remains deferred; original manuscript sources are unchanged.

Verified with Lean v4.36.0-rc2: full build 12235 jobs, direct axiom audit of 8466 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6289 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 13.49 GiB.


## Literal Veronese quotients and plane-equation Hilbert degree

The literal Veronese construction now commutes with quotient by a
homogeneous ideal, after contracting that ideal along the inclusion.
A graded map is restricted to the actual Veronese subalgebras. Its
surjectivity follows by lifting each homogeneous component, rather
than by assuming surjectivity after restriction. The restricted
quotient kernel is proved equal to the contracted ideal. The actual
quotient isomorphism identifies every rescaled homogeneous piece,
including its vector-space dimension.

For a nonzero homogeneous plane equation f of degree e, this constructs
an isomorphism from the native Veronese quotient by the contracted
principal ideal (f) to the literal D-th Veronese of F[X,Y,Z]/(f).
The native quotient therefore has the actual affine Hilbert polynomial
De*T + (3e-e^2)/2 and Hilbert multiplicity De when D,e are positive.
This identifies actual quotient pieces; no Hilbert-degree comparison
is supplied as an assumption.

The remaining geometric step is to extract the homogeneous plane
equation and prove that the actual image prime ideal is its contracted
principal ideal. The Veronese/quotient algebra comparison needed once
that equality is established is now proved. Finite two-parameter
normalization for actual source curve quotients, scheme dimension,
hyperplane-bundle comparison, low-degree geometry and external host
counts remain open. T1.7 stays in_progress, numbered coverage stays
79/167, confirmed mathematical improvements stay 107, and Palomar
remains deferred. Original sources are unchanged.

Verified with Lean v4.36.0-rc2: full build 12241 jobs, direct axiom audit of 8484 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6313 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 13.48 GiB.


## Finite plane normalization and actual source curve degree

Finite two-parameter normalization is now constructed over an infinite
field for an actual homogeneous plane quotient containing a nonzero
homogeneous relation. A checked scaling identity proves nonvanishing
somewhere on the fixed projective affine patch X0=1. An explicit
invertible linear shear preserves every homogeneous degree and makes
the first-variable leading coefficient a nonzero scalar. Its monic
normalization and the actual polynomial quotient isomorphism prove
module finiteness over the remaining linear coordinates.

A polynomial algebra is proved finite over its positive coordinate
powers: each coordinate is integral over its power, and the actual
finite coordinate family generates the algebra. For an algebra already
finite over linear parameters, their D-th powers give a finite action
on the actual ambient algebra. Its literal Veronese embeds linearly
into that finite module over a Noetherian polynomial ring, so it is
finite too. The same parameters are proved to have rescaled degree one.
This supplies actual finite parameters, rather than assuming them.

Finite parameters transfer through the checked Veronese quotient
isomorphism and through actual finite graded maps. The actual source
prime quotient map is constructed as an F-algebra map and is proved
finite from its existing homogeneous generators. Hence it inherits
finite parameters and an actual Hilbert polynomial from its native
base quotient.

When the actual base ideal is the contraction of the principal ideal
of a nonzero homogeneous plane equation f of positive degree e, the
native base has the explicit affine Hilbert polynomial
De*T+(3e-e^2)/2, and source Hilbert-polynomial existence is now proved
from that ideal equality. Neither Hilbert existence nor an assumed
Hilbert slope remains a separate input. The actual source Hilbert
multiplicity is proved equal to D*e times the degree of the actual
projective function-field map between the literal quotient Proj schemes.
The stored public theorem states this literal field finrank, verified
by inspecting its elaborated type and kernel axioms.

This discharges the Hilbert-existence and Veronese-quotient comparison
steps for an identified plane-equation image. Extracting that equation
from the actual geometric curve image prime remains open; the image
ideal equality is still an explicit premise. Scheme dimension,
hyperplane-bundle comparison, low-degree geometry and external host
counts remain open. T1.7 stays in_progress, coverage stays 79/167,
confirmed improvements stay 107, and Palomar remains deferred.
Original manuscript sources are unchanged. No new Paper C code is reused;
the adapted homogeneous top-coefficient argument is attributed to the
pinned Mathlib source with its Apache licence.

Verified with Lean v4.36.0-rc2: full build 12269 jobs, direct axiom audit of 8532 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6372 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 15.21 GiB.


## Actual source prime heights and extracted plane-equation degree

The actual homogeneous prime ideals now pass through the checked
Veronese projective isomorphism. Its underlying point equivalence is
constructed, and the contraction of its inverse prime is proved to be
the original Veronese prime. For an actual source prime quotient, a
nonzero degree-one base quotient coordinate constructs its projective
base prime. Its inverse gives an actual homogeneous prime in the
ordinary three-variable plane ring, with contraction exactly equal to
the actual base ideal.

A nonzero principal homogeneous polynomial ideal is proved to have a
homogeneous generator. The proof takes a nonzero homogeneous component
of a generator. Divisibility by the generator and additivity of total
degree force the quotient to be a nonzero constant. The generator is
therefore a scalar multiple of that homogeneous component. For a proper
ideal its degree is positive. The pinned UFD height-one theorem then
produces a positive-degree homogeneous generator of a height-one prime;
primality of the principal ideal proves the generator irreducible.

Prime contraction is strictly increasing along chains under integral
maps. The actual height inequality is proved using order height. With
going down, chains lift and the heights are equal. The actual source
projection has both properties: its checked finite free basis supplies
integrality and flatness, hence going down. Therefore the actual source
prime and its native base contraction have equal heights. Every positive
Veronese inclusion is also proved integral by taking D-th powers of
homogeneous elements and recomposing arbitrary elements. The lifted
ordinary plane prime has height at most the native base prime. If the
source prime has height one, its base contraction is nonzero of height
one, so the lifted ordinary plane prime is nonzero and has height one.

Consequently a height-one actual source prime supplies its own
homogeneous irreducible plane equation and the exact contracted-ideal
equality. Over an infinite field, source Hilbert-polynomial existence
then follows from the preceding finite-normalization proof. The actual
source Hilbert multiplicity equals D times the extracted equation degree
times the actual projective function-field degree. The final theorem
assumes neither a plane equation, an image ideal equality, an image-height
condition, a Hilbert polynomial nor a slope. The source-height-one input
and a nonzero degree-one base quotient coordinate remain explicit.

The algebraic image-equation extraction is thus complete in this
source-height-one formulation. A separate statement-alignment step must
relate the manuscript's geometric dimension-one curve condition to that
source prime height, and compare the actual Hilbert multiplicity with
the intrinsic hyperplane degree. Low-degree geometry and external host
counts remain open. T1.7 stays in_progress, coverage stays 79/167,
confirmed improvements stay 107 and Palomar remains deferred. Original
manuscript sources are unchanged.

Verified with Lean v4.36.0-rc2: full build 12297 jobs, direct axiom audit of 8555 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6399 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 15.18 GiB.


## Actual projective curve points and their constructed chart coordinates

The source curve degree theorem now takes an actual projective source
point and the height-one condition on its homogeneous prime. The point
itself supplies primality, homogeneity, and relevance. Its image under
the actual source projection is a relevant native Veronese prime.

For any internally graded algebra generated in degree one, relevance
of a quotient ideal is proved to yield a nonzero degree-one quotient
coordinate: otherwise all degree-one generators would lie in the ideal,
forcing it to contain the irrelevant ideal. The native base satisfies
the required generation theorem. An actual nonzero base coordinate is
therefore constructed from the source projective point and its actual
projection. No coordinate witness is a separate theorem input.

The resulting theorem constructs the homogeneous irreducible plane
equation, proves the actual base ideal equals its contracted principal
ideal, proves source Hilbert-polynomial existence, and identifies the
actual source Hilbert multiplicity with D times the extracted plane
equation degree times the actual projective function-field degree.
The stored public statement uses literal quotient Proj function fields;
its elaborated type and kernel axioms are inspected directly.

The remaining statement-alignment steps concern the geometric curve
dimension versus homogeneous prime height and intrinsic hyperplane
degree versus the actual coordinate Hilbert multiplicity. Low-degree
curve geometry and the external uniform host counts remain open.
T1.7 stays in_progress, numbered coverage stays 79/167, confirmed
mathematical improvements stay 107, and Palomar remains deferred.
Original manuscript sources are unchanged.

Verified with Lean v4.36.0-rc2: full build 12303 jobs, direct axiom audit of 8565 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6413 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 15.17 GiB.


## Actual small-degree curves and degree-one function-field square descent

For an actual height-one projective source point, source Hilbert
multiplicity below 2D now forces a homogeneous linear irreducible
plane-image equation and actual projective function-field degree one.
The proof uses the already established literal degree formula and the
positive integer factors; it assumes no line equation or birationality.

A degree-one field extension is proved to be an actual algebra
isomorphism and to reflect squares and quadratic roots. The generic
finite graded-map rank comparison is used to construct the isomorphism
of its actual projective function fields when module rank is one.
This is specialized to the actual source-point projection. The public
square-reflection theorem concerns the literal quotient Proj function
fields and their actual scalar map. It requires no infinite-field
assumption. The public elaborated types and kernel axioms are inspected
directly. Instance-preserving generic specialization avoids rebuilding
large stalk-map expressions in handwritten source-point field types.

Thus a source curve below 2D has the linear image and degree-one field
map needed for the next exclusion step. The existing functional-square
line obstruction still needs the checked affine line parametrization
and the actual curve-coordinate/function-field diagram before it can
exclude all such curves through admissible hosts. This geometric
exclusion is not claimed here. Geometric dimension/prime-height and
intrinsic hyperplane-degree/Hilbert-multiplicity alignment, higher
low-degree geometry, and the external uniform host counts remain open.
T1.7 stays in_progress, coverage stays 79/167, confirmed improvements
stay 107 and Palomar remains deferred. Original sources are unchanged.

Verified with Lean v4.36.0-rc2: full build 12311 jobs, direct axiom audit of 8573 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6425 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 15.15 GiB.


## Actual radical descent, affine quotient charts, and graph-line exclusion

The literal homogeneous radical equations are now proved in the actual
source and base curve quotients. For a finite graded projection of rank
one, these equations descend to squares in the actual projective base
function field on any nonzero degree-one chart. This is specialized to
an actual projective source point and its actual degree-one field map.

For any surjective graded map, the kernel of the actual degree-one
chart map is proved to be the image of the graded-map kernel under
dehomogenization. The actual native Veronese quotient Z-chart is thereby
identified with the affine polynomial-plane quotient. Contracting a
homogeneous principal plane ideal and then taking this chart gives
exactly the principal ideal of its affine equation, for any homogeneous
equation degree and any positive Veronese degree.

For a plane-image ideal whose affine equation is Y = alpha X + beta,
the actual base chart is constructed as a polynomial ring in one
variable. Its nonzero chart coordinate follows from the image-ideal
condition. The chart equivalence sends every literal radicand to exactly
the line-restriction polynomial used in the proved square obstruction.
The actual source degree-one projection therefore produces functional
squares in the ordinary rational function field, without separate
square or coordinate-diagram assumptions. Over the rationals, the
admissible-host square-class and disjoint-support hypotheses contradict
this. An actual height-one source curve with such a graph-line image
through an admissible host has Hilbert multiplicity at least 2D.

The graph-line image ideal and host-on-line conditions remain explicit.
The classification of an arbitrary homogeneous linear image into a
graph or vertical line, and the corresponding actual vertical-chart
diagram, remain open. So do geometric dimension/prime-height and
intrinsic hyperplane-degree/Hilbert-multiplicity alignment, higher
low-degree geometry, and external uniform host counts. T1.7 remains
in_progress, coverage stays 79/167, confirmed improvements stay 107,
and Palomar remains deferred. Original sources are unchanged.

Verified with Lean v4.36.0-rc2: full build 12331 jobs, direct axiom audit of 8599 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6464 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 15.12 GiB.


## Actual full low-degree exclusion through affine source points

The actual vertical base-curve chart is now constructed as a polynomial
ring in one variable. Its equivalence sends each literal radicand to
the polynomial used in the existing vertical functional-square
obstruction. Degree-one projection of the actual source curve gives
these functional squares, without separate square or chart-coordinate
assumptions. The admissible-host hypotheses exclude this projection.

A homogeneous polynomial of degree one is proved to equal its literal
linear coefficient form. On the native Z-chart, a nonzero such equation
through an affine point is classified exhaustively as a graph line
through that point or the corresponding vertical line, including the
horizontal case. Multiplication by the appropriate nonzero scalar is
proved to preserve the exact principal ideal.

Combining this classification, the previously established actual curve
degree formula, and both actual chart-square diagrams proves the full
coordinate-algebraic version of Step 3: an actual height-one projective
source curve whose affine image contains an admissible rational host
has Hilbert multiplicity at least 2D. No line, plane equation,
birationality, or functional-square witness is an input. Both block
independence conditions, direct sum, nonzero coefficients, at least two
equations, and both disjoint nonempty support families are explicit.

The containment condition is also proved from an actual affine point
of the split-radical source with its literal base evaluation and an
actual source-curve ideal contained in that point's evaluation kernel.
The actual affine source point restricts to a map on the homogeneous
source Veronese ring, and its base image is proved to be the literal
affine host evaluation. Thus the projection/point containment diagram
is checked, rather than an independent assumption in the degree bound.

The previously open vertical diagram and linear-image classification
are discharged. Geometric curve dimension versus source prime height
and intrinsic hyperplane degree versus coordinate Hilbert multiplicity
still require statement alignment. Higher low-degree curve geometry
and external surface/curve uniform point counts remain open. T1.7
stays in_progress, coverage stays 79/167, confirmed mathematical
improvements stay 107, and Palomar remains deferred. Original sources
are unchanged.

Verified with Lean v4.36.0-rc2: full build 12349 jobs, direct axiom audit of 8623 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6496 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 15.10 GiB.


## Actual embedded-curve coordinate quotients and degree comparison

The actual ambient homogeneous coordinate ideal of a source curve is
now constructed as the preimage of its source prime under exactly the
polynomial evaluation map defining the chosen projective embedding.
Its coordinate quotient is constructed as an algebra isomorphic to the
actual source prime quotient, with a linear equivalence of every pair
of corresponding graded pieces. These constructions work for general
homogeneous ideals; no primality or Hilbert polynomial is assumed for
the coordinate algebra comparison itself.

For an actual source projective point, the ambient coordinate ideal is
proved to be the ideal of its actual image under the chosen embedding.
It is prime and projectively relevant and contains the global source
embedding relations. Thus the coordinate quotient is attached to the
actual embedded image point, rather than an unrelated presentation.

Equality of the actual graded-piece dimensions transports Hilbert
polynomial existence, the polynomial itself, and its multiplicity.
For an actual height-one source point this gives the ambient curve
coordinate Hilbert polynomial, its multiplicity equality with the
source quotient, and the literal degree formula D times the plane-image
equation degree times the actual projective function-field degree.
Over the rationals, the full low-degree exclusion through an actual
admissible affine source point therefore yields multiplicity at least
2D in the actual ambient homogeneous coordinate presentation as well.

The curve-level comparison with the chosen projective coordinate
presentation is now discharged. A separate intrinsic line-bundle
intersection-degree theory is not constructed or claimed here.
Geometric curve dimension versus homogeneous source prime height,
higher low-degree curve geometry, and external surface/curve uniform
point counts remain open. T1.7 stays in_progress, numbered coverage
stays 79/167, confirmed mathematical improvements stay 107, and Palomar
remains deferred. Original manuscript sources are unchanged.

Verified with Lean v4.36.0-rc2: full build 12361 jobs, direct axiom audit of 8648 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6529 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 15.08 GiB.


## P1-MATH-0108 — Explicit grid-uniform rational interpolation

A bounded-degree rational function is now proved to be determined by
more than twice its degree many distinct abscissae. The cross product
of two interpolating polynomial pairs vanishes by its actual degree
and roots. For a reduced pair of exact maximum degree a with nonzero
denominator, every other interpolating pair of degrees at most a is
an actual constant scalar multiple. The actual linear interpolation
constraint map on the bounded-polynomial pair space is constructed;
its kernel is proved to equal the span of that pair and has dimension
one.

An elementary bounded integer-kernel construction is proved for every
integer matrix with t rows and t+1 columns: entries of absolute value
at most H yield a nonzero integer kernel vector whose coordinates have
absolute value at most (3(t+1)H)^t. This extends the existing explicit
pigeonhole proof to the codimension-one regime needed for interpolation.

For 2a+1 integer grid points with distinct abscissae and both coordinates
of absolute value at most B, B at least one, the actual interpolation
matrix has 2a+2 columns and entry height at most B^(a+1). Its bounded
integer kernel gives actual integral polynomials P,Q, Q nonzero, of
degrees at most a, with every coefficient bounded by
(3(2a+2))^(2a+1) B^((a+1)(2a+1)). If a reduced rational pair of exact
degree a fits that grid, these integral polynomials map to a common
nonzero rational scalar multiple of that pair. Their rational images
are proved coprime and retain exact maximum degree a. The coefficient
bound therefore depends on the grid and degree alone, independently
of the original rational coefficients or auxiliary radical coefficients.

This supplies an explicit alternative proof of the coefficient-uniform
interpolation step in Step 6. It does not establish the preceding
normalization, genus, branching, reduced-fibre or rational-graph
conclusions. The remaining geometric dimension/prime-height and any
intrinsic line-bundle degree interpretation are separate; external
uniform point counts also remain open. T1.7 stays in_progress, numbered
coverage stays 79/167, confirmed mathematical improvements become 108,
and Palomar remains deferred. Original sources are unchanged.

Verified with Lean v4.36.0-rc2: full build 12373 jobs, direct axiom audit of 8673 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6561 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 15.06 GiB.


## Grid-uniform rational-graph exclusion after interpolation

The arithmetic alternatives following rational interpolation in Step 6
are now proved for actual rational polynomial pairs and integral points.
For integral numerator and denominator polynomials whose rational images
are coprime, the denominator value at an integral graph point divides
the actual nonzero resultant. The existing determinant height bound
therefore bounds that value uniformly. A nonconstant integer polynomial
of coefficient height M taking a value of absolute value at most K has
its integer input bounded by M+K, via the verified integral-root bound.
Consequently a nonconstant rational denominator gives an explicit
abscissa bound M+(2a)! M^(2a).

For a polynomial graph of exact degree a at least two, the nonzero
integral leading coefficient and a bounded coefficient tail prove
|X|^a <= |P(X)|+a M |X|^(a-1). At an integral graph point with
|Y| <= 2|X| and constant denominator of height at most M this gives
|X| <= (a+2)M. The actual integral presentation from the grid is proved
to preserve both degrees and every original integral graph equation.

The remaining linear graph is treated directly from two actual offset
grid matches. They give proportional positive selected values at the
host; independence and direct sum contradict this. This argument takes
no functional-square premise and no degree-one curve-field assumption.

All cases are combined: for every positive exact rational-function
degree a and 2a+1 distinct offset abscissae, the actual reduced rational
graph fitting the grid has no admissible comparable integral host with
abscissa larger than an explicit polynomial in the offset height B.
Writing C=(3(2a+2))^(2a+1), its bound is at most
[C+(2a)! C^(2a)+(a+2)C] B^(2a(a+1)(2a+1)). This is uniform in the
original rational coefficients and all auxiliary radical coefficients.

Thus the elementary interpolation and subsequent arithmetic rational-
graph exclusion in Step 6 are checked. The geometric work producing
that reduced rational graph and its offset-grid matches from a general
low-degree source curve, including genus, branching and reduced-fibre
arguments, remains open. Geometric curve dimension/source prime height,
any intrinsic line-bundle intersection degree interpretation, and the
external surface/curve point counts also remain open. T1.7 stays
in_progress, coverage stays 79/167, confirmed improvements stay 108,
and Palomar remains deferred. Original sources are unchanged.

Verified with Lean v4.36.0-rc2: full build 12391 jobs, direct axiom audit of 8691 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6581 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 15.04 GiB.


## Rational descent, surviving equation grids, and uniform critical exclusion

The arithmetic graph cutoff is now converted to an actual uniform
large-scale exclusion in the critical band. If the offset height is
at most (L+1)^J and L differs from log(N)/log(2) by at most C, then
one threshold, chosen before all coefficients, grids and hosts,
excludes admissible graph points with X>=N and |Y|<=2N.

The interpolation also descends coefficients: over every field F of
characteristic zero, a reduced rational polynomial pair of exact
maximum degree a fitting 2a+1 bounded integer grid points is a common
nonzero F-scalar multiple of an actual bounded integral pair. The
rational images of that integral pair are proved coprime. This gives
an actual reduced pair over the rationals with the same exact degree,
whose images under the rational embedding into F are the stated
scalar multiples. Its integral graph-point condition is proved
exactly equivalent to the original one. Rationality of the initial
graph's coefficients is therefore not a separate input.

The finite selection of the interpolation grid is also constructed.
Three disjoint root families of cardinality a>=1 give at least 3a
grid points with distinct first coordinates; an actual 2a+1-point
subfamily is selected. If the initial number of equations is at least
4(E+1)^2 and at most 2e^2 are excluded, e<=E, the actual surviving
set has at least three equations. No assumed grid-selection map or
survivor-count witness remains.

These results are combined for the actual disjoint equation-root
families and their actual exceptional set. A single large-scale
threshold excludes the resulting graph host, uniformly over all
characteristic-zero coefficient fields, equation families, excluded
sets, numerator/denominator coefficients, and admissible hosts. It
retains the exact root-family disjointness, cardinalities, positivity,
selected-value independence, direct sum, critical band and offset
height hypotheses. The numeric exceptional-set bound and the reduced
graph with its actual root matches are explicit hypotheses: the
preceding genus, branching, reduced-fibre, and graph-construction
geometry has not been supplied or counted as complete.

T1.7 stays in_progress, numbered coverage stays 79/167, confirmed
mathematical improvements stay 108, and Palomar remains deferred.
Geometric curve dimension/source prime height, any intrinsic
line-bundle degree interpretation, and the external uniform
surface/curve point counts also remain open. Original sources and
the Lean/Mathlib pins are unchanged.

Verified with Lean v4.36.0-rc2: full build 12403 jobs, direct axiom audit of 8708 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6601 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 15.02 GiB.


## Actual field-degree tower and direct common-quotient graph construction

The rational-function degree tower in Step 5 is now proved for
actual intermediate fields. For a reduced pair p,q over any field F,
q nonzero, the degree of F(T) over F(p/q) is max(deg p,deg q), using
the proved Mathlib rational-function degree theorem and an explicit
comparison with the supplied reduced pair. Evaluating at an actual
transcendental x in an extension K transports this to F(x)/F(p(x)/q(x)).
The tower identity for the actual extension K follows; positive degree
of K/F(x) permits exact cancellation in the manuscript's mY=a*mX.

A more direct algebraic construction is also proved. Write
A_nu=b_nu product_{i in I_nu}(T+i), with nonzero b_nu in F, disjoint
root sets of the same positive cardinality a, and actual identities
A_nu(x)=t*(y+j_nu). Two equations suffice to construct
q=A_0-A_1 and p=j_0*A_1-j_1*A_0. The denominator is nonzero;
j_0 and j_1 are proved distinct, rather than assumed distinct.
The pair p,q is coprime and has exact maximum degree a. Every further
equation gives the actual polynomial identity
p+j_nu*q=(j_0-j_1)*A_nu. Thus all selected offsets give the required
grid matches, and coprimality proves the denominator nonzero there.
The natural input in which the original quotients differ by nonzero
F-constants is converted to these identities as well. Exact graph
degree and all root matches therefore follow algebraically after
the common-quotient step, without a separate curve-degree cancellation.

The graph relation C(p)-Y*C(q) is proved to lie in the actual kernel
of evaluation at the function-field coordinates. Every integral
point whose evaluation kernel contains that actual coordinate ideal
satisfies the graph equation. Combining the constructed reduced graph,
all its constructed matches, actual survivor/grid selection, rational
descent and the preceding arithmetic bounds gives an explicit offset-
only bound on admissible integral curve points. Its critical-band
large-scale exclusion chooses one threshold before both fields F,K,
the equations, constants, exceptional set, coordinates and hosts.
There is no assumed reduced graph, exact graph degree, grid-match map,
or graph-point equation in this final common-quotient exclusion.

This is recorded as improvement P1-MATH-0109, a simplification of the
transition between Steps 5 and 6. The geometric arguments providing
nonconstant/transcendental x, the common-quotient constants from equal
divisors, and the exceptional-equation bound remain explicit open
work. Genus, Riemann--Hurwitz, reduced-fibre/divisor arguments,
geometric dimension versus source prime height, intrinsic line-bundle
degrees and the external uniform point counts are not claimed proved.
T1.7 stays in_progress, coverage stays 79/167, confirmed improvements
become 109, and Palomar remains deferred. Original manuscript bytes
and the Lean/Mathlib pins are unchanged.

Verified with Lean v4.36.0-rc2: full build 12421 jobs, direct axiom audit of 8740 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6639 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 14.99 GiB.


## Actual affine-curve equation, fraction field, and common-quotient exclusion

The common-quotient exclusion now applies to the actual coordinate
domain F[X,Y]/(C) and its actual fraction field, for an irreducible
plane equation C over any characteristic-zero field. The generic
coordinates are constructed from the quotient and fraction maps;
their actual evaluation kernel is proved to be the principal ideal
(C). Positive degree in Y proves the first coordinate transcendental.
Every actual integral point satisfying C(X,Y)=0 gives the exact kernel
containment needed to specialize the constructed graph equation.
Thus neither transcendence of an abstract coordinate nor an assumed
coordinate-ideal containment remains in the actual-curve cutoff.

The graph relation p(X)-Y*q(X) is proved irreducible when p,q are
coprime and q is nonzero. A relation in the actual curve function
field makes C divide this polynomial, so the actual irreducible C is
associated to the graph relation. Its degree in Y is proved exactly
one, and its points are proved exactly equivalent to the cross-
multiplied graph equation. This identifies the actual plane equation,
rather than only supplying a rational function with selected matches.

Both generic coordinates are proved to generate the entire actual
fraction field: every fraction is represented by quotient classes of
two actual bivariate polynomials. When the second coordinate satisfies
the graph relation, the first coordinate alone generates that field.
An actual F-algebra equivalence with RatFunc F is constructed, sending
the rational indeterminate to the actual first coordinate.

The explicit admissible-integral-point bound and the critical-band
exclusion are assembled for this actual curve equation and actual
fraction field. The large-scale threshold precedes the coefficient
field, the curve equation, all equation data, constants and hosts.
Curve-coefficient height and auxiliary coefficient height do not
enter it. The remaining geometric input is still the common-quotient
identities and the bounded exceptional set. Their derivation from the
original radical source curve, its genus/branching/divisor theory,
and the final uniform point counts remain open. Rationality here
concerns the plane image's function field, not the function field
of the radical source cover. This extends P1-MATH-0109; it adds no
new numbered coverage or separate finding. Coverage stays 79/167,
confirmed improvements stay 109, T1.7 stays in_progress, and Palomar
remains deferred. Original sources and compiler/dependency pins are
unchanged.

Verified with Lean v4.36.0-rc2: full build 12431 jobs, direct axiom audit of 8759 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6665 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 14.97 GiB.
