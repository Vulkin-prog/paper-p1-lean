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
