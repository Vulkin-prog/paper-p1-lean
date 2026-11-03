# Actual projective scheme map

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

## Upstream provenance and statement comparison

The generic scheme construction adapts
`Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Functor.lean` at the
immutable Mathlib commit
`9d581dfff2e41de989072ea63abf3daf69311520`, matching Lean
`v4.36.0-rc2`. Upstream copyright (c) 2026 Kenny Lau and the Apache
2.0 license notice are retained in `Geometry/ProjRadicalMap.lean`;
the repository LICENSE is Apache 2.0. The dependency is unchanged.

The upstream hypothesis is containment of the source irrelevant
ideal in the mapped base irrelevant ideal. The local version takes
containment in its radical, proves the necessary contradiction at
every homogeneous prime, and makes the dependent point, sheaf and
stalk constructions use that proved point map. The actual source
module supplies this hypothesis by its checked quadratic equations.
No unproved algebraic-geometric input is introduced, and no further
Paper C source is reused. Compilation, axiom inspection and ledger
reference checks use the pinned rc2 toolchain.

Verified with Lean v4.36.0-rc2: full build 11821 jobs, direct axiom audit of 8089 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 5799 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 13.95 GiB.

Audit discovery also includes theorem and lemma attributes on the same
line as their declaration. This adds seven older auxiliary declarations
to direct axiom inspection, along with all twelve declarations in this
checkpoint; it changes neither mathematical statements nor coverage.


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

The first three proofs in `Geometry/ProjRadicalCharts.lean` adapt
the basic-open and localization compatibility proofs from the same
upstream Functor.lean file and pinned Mathlib commit recorded above.
The copyright and Apache 2.0 attribution are preserved. The new
dehomogenization and finiteness arguments are proved locally;
Mathlib's definition of finite scheme morphisms, its affine Spec
criterion and its Zariski locality supply the checked scheme API.
No external arithmetic estimate, original source change or further
Paper C port is introduced. Additional Mathlib dependencies were
compiled selectively, without downloading the full cache.


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

These modules use the pinned Mathlib quotient tensor-product
equivalences, basis base change, flat ring and scheme criteria,
scheme chart pullbacks and finite-flat rank API. In particular the
rank is the existing Mathlib scheme definition, not a new function
defined to have the desired value. All compatibility maps and
their hypotheses are discharged on the actual source. No new
unproved literature input or Paper C port is introduced; additional
Mathlib dependencies are compiled selectively. Manuscript V1.6
is preserved byte for byte.


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

The function field in these statements is Mathlib's existing
Scheme.functionField, the stalk of the actual generic point.
The proofs use the pinned Proj stalk isomorphism and the existing
scheme integrality and function-field API. The projective function
field map is the actual stalk map of the previously constructed
scheme morphism after the proved generic-point equality. No new
axiom, arithmetic estimate, Paper C port or original source edit
is introduced. Dependencies are compiled selectively on Ubuntu.


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


## Quantitative square-class descent and even actual line-projection degree

A quantitative square-class descent theorem is now proved. For
independent nonzero square classes over a characteristic-zero field
K whose images become squares in E, the actual independent radical
tower embeds in E. Therefore 2^r divides the actual degree [E:K],
where r is the number of independent classes. The actual linear map
on field square classes is constructed from the unit map and the
quotient by doubles. Its entire kernel is proved finite-dimensional
for every finite extension, and 2^(dimension of that kernel) divides
[E:K]. In particular its dimension is at most floor(log_2 [E:K]).
Finiteness of the kernel is proved, not assumed as an extra input.

The odd-degree consequence is proved separately in every
characteristic: a nonsquare acquiring a square root forces 2 to
divide the actual field degree, by the actual two-dimensional
quadratic algebra and the tower law. Hence every odd-degree field
extension reflects squares. This assertion needs no characteristic-
zero assumption and no asserted field isomorphism.

The odd-degree reflection is transported through the actual graded
projective function-field degree comparison and actual chart maps.
The literal radical equations consequently descend on graph-line
and vertical-line charts whenever the actual source-to-image field
degree is odd. Their actual polynomial restrictions are squares in
the corresponding rational-function fields. The selected-value
independence and direct-sum obstruction excludes both cases at the
actual admissible integral host. Exhaustive classification of the
actual homogeneous linear image then proves that every source
projection onto a line through such a host has even actual field
degree. The line, host, nonzero coefficients, selected nonempty
disjoint root families, positivity and both injectivity assumptions
remain explicit. The former degree-one theorems are corollaries
of these stronger results and retain their existing statements.

This is improvement P1-MATH-0110: Step 3's degree-one obstruction
extends to every odd projection degree, and the general square-class
kernel receives a quantitative degree bound. It does not replace the
remaining higher-curve genus/branching/divisor arguments, exceptional-
equation estimates or external uniform point counts. T1.7 remains
in_progress, numbered coverage stays 79/167, confirmed improvements
become 110, and Palomar remains deferred. Original manuscript bytes
and the Lean/Mathlib pins are unchanged.

Verified with Lean v4.36.0-rc2: full build 12445 jobs, direct axiom audit of 8787 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6695 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 14.95 GiB.


## Rational square graphs: actual pole deletion, arbitrary-degree interpolation, and odd-extension exclusion

The odd-degree descent now also gives a checked arithmetic
exclusion for every bounded-degree rational graph. This route takes
the actual split-product radical equations in an actual field
extension of F(T), whose degree is odd; it does not assume common
quotients, an exceptional-equation budget or interpolation matches.
Odd-degree reflection makes the literal rational functions
c_nu product(T+i)*(p/q+j_nu) squares in the actual fraction field.

Clearing the actual nonzero denominator squared and reflecting
squares to F[T] yields a polynomial square. Its derivative vanishes
at each selected root. The split root is proved simple, so whenever
q(-i) is nonzero this forces p(-i)=-j_nu*q(-i). The actual equations
whose selected root sets meet a denominator zero are constructed;
disjointness gives an injection into the actual roots of q and
proves that at most deg(q) equations are lost. No assumed pole-
exclusion set or assumed cardinal estimate is used.

If d=max(deg p,deg q) is at most E and there are at least 3E+1
equations with disjoint nonempty root sets of a common cardinality,
the actual survivors supply 2d+1 distinct offset abscissae. The
requested grid selection is constructed for arbitrary grid size,
so the root-family cardinality need not equal d. The constant graph
case is itself excluded by one radical equation and positivity at
the actual host; positive graph degree is derived, not assumed.
Actual rational descent then gives the preceding explicit offset-
only abscissa bound. One critical-band threshold works for every
d<=E, and is chosen before both coefficient/extension fields, the
root-family degree, the graph coefficients, all radical coefficients,
all selected data, the odd extension degree and all hosts.

The final statement uses actual radical roots in the specified odd-
degree extension and the actual integral graph-point equation. The
transport from a general source curve to such a rational image is
not assumed established. Even-degree extensions and nonrational
images still require further geometry. This extends P1-MATH-0110;
it adds no numbered coverage or separate finding. T1.7 remains
in_progress, coverage stays 79/167, confirmed improvements stay 110,
and Palomar remains deferred. Original source bytes and pins are
unchanged.

Verified with Lean v4.36.0-rc2: full build 12461 jobs, direct axiom audit of 8804 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6714 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 14.93 GiB.


## Actual curve radical transport and eventual even rational-image cover degree

The odd-degree rational-image exclusion is now transported from
the rational-function presentation to an actual irreducible plane
curve equation and its actual fraction field. An explicit F-algebra
equivalence from FractionRing F[T] to that curve field is constructed
for a supplied reduced graph presentation in its actual generic
coordinates. Its value on every polynomial is proved to be actual
evaluation at the generic first coordinate. The actual rational
quotient is proved to equal the generic second coordinate.

The literal scaled split-radical polynomial c*P_I(X)*(Y+j) is
transported exactly to the rational-graph function used in the
preceding pole-deletion argument. Squarehood is equivalent under
this actual field equivalence. Thus actual radical roots in an
actual odd-degree extension of the curve field provide the precise
functional squares; no unidentified scalar map or separately assumed
functional-square premise remains. The host graph equation follows
from the actual point condition C(X,Y)=0 by the proved identification
of C with its reduced graph relation.

The final uniform statement excludes actual integral curve points
under the literal radical equations in that odd-degree cover. Its
threshold precedes the curve equation, both fields, all reduced
graph coefficients, the radical roots and coefficients, the common
root-family degree and the host data. The graph's maximum degree
is bounded by E; it is not required equal to the root-family degree.
A corresponding theorem states the actual finite cover degree must
be even at every such sufficiently large admissible host.

This extends P1-MATH-0110 without a new finding or numbered result.
It does not assert that a general source curve has a graph image,
nor identify all source-scheme cover maps with this affine fraction-
field presentation. The even-degree and non-graph image geometry,
general degree comparisons and external uniform point counts remain
open. T1.7 stays in_progress, coverage stays 79/167, confirmed
improvements stay 110 and Palomar remains deferred. Original sources
and the compiler/dependency pins remain unchanged.

Verified with Lean v4.36.0-rc2: full build 12467 jobs, direct axiom audit of 8811 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6722 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 14.91 GiB.


## Bounded radical covers force graph images through actual square-class kernels

A new algebraic route proves the graph-image conclusion in the
nonconstant-coordinate branch of Step 5, including even cover degrees.
Let C be an actual irreducible integer plane equation of positive
degree in both coordinates, K its actual quotient fraction field,
and L an actual finite extension containing the literal scaled
radical roots d_nu*P_I_nu(X)*(Y+j_nu). The integer coefficients are
nonzero, the selected first-root sets are disjoint and nonempty,
and the singleton second offsets j_nu are distinct.

The actual square-class map from binary equation selectors is
constructed. Its image lies in the actual square-class kernel for
L/K, so its rank is at most log_2[L:K]. A finite linear argument
proves that on a subspace of codimension s, at most 2s coordinate
forms vanish or coincide with another coordinate form. The actual
remaining nonzero distinct coordinate forms separate one selected
equation from every other equation by a kernel word.

The formal-branch matching argument is extended to every actual
nonzero integer scalar multiplying a word. For a good coordinate,
every root of every regular selected first fibre must equal that
equation's own second offset: one kernel word gives an offset match,
and a second word selecting this equation while omitting a proposed
different equation rules out every other match. The existing actual
separability and exact fibre-root count then prove deg_Y(C)=1.
No genus, Riemann--Hurwitz, divisor-constant or common-quotient
hypothesis is used in this conclusion.

The exceptional equation sets are constructed. Disjoint first-root
sets give an actual injection of equations meeting bad first fibres
into the actual critical-offset set. The total loss is at most
2 floor(log_2[L:K]) plus the cardinality of that critical set, bounded
by deg_X(C)+2 deg_X(C)deg_Y(C). If both partial degrees and the actual
cover degree are at most E and there are at least 4(E+1)^2 equations,
the actual good family has at least 2E+1 equations. Each selected
offset in every good equation is proved an actual integer point
C(-i,-j_nu)=0, and the plane image is proved a graph.

This is improvement P1-MATH-0111, an alternative to the genus and
common-quotient part of Step 5 for the stated nonconstant-coordinate
and bounded-degree presentation. It has not yet supplied the general
source-scheme identification, bounds comparing the actual ordinary
ambient curve degree to both image and extension degrees, the
constant-coordinate cases, or the complete subsequent graph
interpolation for arbitrary cover degree. Those and the external
uniform point counts remain open. T1.7 stays in_progress, numbered
coverage stays 79/167, confirmed improvements become 111 and Palomar
remains deferred. Original sources and pins remain unchanged.

Verified with Lean v4.36.0-rc2: full build 12483 jobs, direct axiom audit of 8845 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6771 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 14.90 GiB.


## Actual reduced graph construction and complete nonconstant bounded-cover exclusion

The new bounded-cover argument is now connected through actual
reduced rational interpolation to a uniform large-scale exclusion.
For an actual irreducible integer plane equation C with deg_Y(C)=1,
the original rational numerator and denominator are constructed from
its actual coefficients. The denominator is proved nonzero at every
actual integer curve point: otherwise both coefficients vanish at
the integer first coordinate, forcing a forbidden vertical factor
of the irreducible equation. No coefficient-height bound is used.

The actual quotient is canonically reduced using its rational-
function numerator and denominator. Their coprimality and nonzero
denominator are supplied by the actual rational-function data.
Both degrees cannot increase under reduction, and the exact
cross-product identity transports every actual curve point and
selected offset match to the reduced pair. Thus its maximum degree
is bounded by deg_X(C), without separately assuming the original
integer coefficient polynomials coprime. One offset match and host
positivity exclude a constant reduced graph.

Combining this construction with the actual good equation family
proves an offset-only abscissa bound for every finite cover degree,
including even degrees. If both positive plane partial degrees and
the actual finite cover degree are at most E, there are at least
4(E+1)^2 literal radical equations, first-root families are disjoint
of a common positive cardinality and singleton second offsets are
distinct, the actual good families supply the reduced graph's
2n+1 interpolation points with 1<=n<=E. The root-family cardinality
is not required equal to n. The original radical coefficients are
arbitrary nonzero integers.

A single critical-band threshold, chosen before the integer curve
equation, all its coefficients, the actual extension field, the
literal radical roots and coefficients, all offsets and root-family
degrees, excludes every actual admissible comparable integral point
on that curve. This statement has no genus, Riemann--Hurwitz,
common-quotient, assumed graph, supplied grid, exceptional-set count,
odd-degree, or graph-coefficient-height premise. All those algebraic
and arithmetic constructions for the stated nonconstant-coordinate
presentation are proved internally.

This extends P1-MATH-0111. The constant-coordinate image cases,
general source-scheme identifications, comparisons between ordinary
ambient curve degree and the actual plane/field degree bounds, and
the external uniform point counts remain open. The numbered T1.7
geometric count is not marked complete. Coverage stays 79/167,
confirmed improvements stay 111 and Palomar remains deferred.
Original manuscript bytes and compiler/dependency pins are unchanged.

Verified with Lean v4.36.0-rc2: full build 12493 jobs, direct axiom audit of 8859 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6788 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 14.88 GiB.


## Actual constant-coordinate charts and uniform exclusion of all bounded radical covers

The actual-plane/finite-cover exclusion now includes both
constant-coordinate image branches. Over every characteristic-zero
integrally closed domain, the actual fraction-field square classes
of nonzero scalar multiples of disjoint nonempty univariate split
products are proved independent. This includes the integer
coefficient polynomial ring itself. The corresponding literal
radical roots in an actual extension force 2^k to divide its actual
field degree; in a finite extension this gives 2^k <= [L:K].

For an actual irreducible integer plane equation with an integer
point, zero Y partial degree forces its ideal to be the actual
vertical line through that point; zero X partial degree similarly
forces the horizontal line. The actual quotient coordinate rings
are constructed as polynomial rings over Z by explicit kernel and
surjectivity proofs. Their fraction-field equivalences are
constructed and proved to transport every literal specialized
polynomial. No separately supplied rational parametrization or
square-class independence premise is used.

On the vertical line the scalar coefficient is the original
nonzero integer radical coefficient times the selected first split
product at the actual integer point. Host positivity proves it
nonzero, and the distinct singleton second offsets give independent
univariate classes. The horizontal line has the symmetric argument
using disjoint nonempty first-root families and positivity at the
second coordinate. Thus neither constant-coordinate image can
support the bounded actual cover when k >= E. Both positive partial
degrees are derived internally before invoking the nonconstant
graph/interpolation exclusion.

The combined theorem chooses one critical-band threshold before
the actual integer curve, its coefficients, extension field,
literal radical roots, offset families, root-family degree and
hosts, and excludes all actual bounded-plane/field presentations
under the previously explicit degree bounds. This includes every
finite cover degree, with no genus, Riemann--Hurwitz, odd-degree,
assumed graph, supplied grid, coefficient-height or constant-
coordinate restriction.

This extends P1-MATH-0111. General source-scheme identifications,
comparisons between ordinary ambient curve degree and the actual
plane/field degree bounds, and external uniform point counts remain
open. T1.7 stays in_progress, numbered coverage stays 79/167,
confirmed improvements stay 111 and Palomar remains deferred.
Original manuscript bytes and compiler/dependency pins are unchanged.

Verified with Lean v4.36.0-rc2: full build 12503 jobs, direct axiom audit of 8887 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6822 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 14.86 GiB.


## P1-MATH-0112 — Actual ordinary-to-weighted curve Hilbert degree comparison

A literal homogeneous algebra comparison now connects the ordinary
affine-projective embedding in Step 5 to the weighted source used
in the existing degree formula. The substitution fixes X,Y,Z and
sends each weighted radical coordinate w to Z^(D-1)w. A polynomial
of weighted degree n maps to an ordinary homogeneous polynomial of
degree n. When 2<=g=|I|+|J|<=2D, each actual weighted radical
relation maps exactly to Z^(2D-g) times the ordinary homogeneous
relation w^2 Z^(g-2)-c P_I P_J.

An actual homogeneous prime ideal Q of the ordinary polynomial ring
containing these literal relations therefore constructs an actual
map from the weighted radical coordinate algebra. Restricting its
actual Veronese map and quotienting by its actual kernel constructs
the source prime P. Its primality and homogeneity are proved. The
actual quotient map is injective and sends every source piece n
into the ordinary quotient piece D*n. If Z is not in Q, its actual
nonvanishing D-th power constructs a relevant source projective
point with precisely this ideal P.

A numerical Hilbert-slope comparison is proved from the constructed
injections, not supplied as a degree inequality. If the ordinary
curve quotient has actual Hilbert polynomial E*n+beta, the actual
source slope is at most D*E. Combined with the proved finite-rank
projection slope, the extracted plane degree times the actual
cover rank is at most E. In particular each is at most E. For the
constructed source projective point with height(P)=1, its own
irreducible homogeneous plane equation is extracted internally,
and the bound is transported to the actual projective function-
field extension degree through the previously proved comparison.
No plane equation, cover rank inequality, supplied Hilbert-piece
dimension inequality, coordinate-degree comparison or coefficient
height bound is an input to this final extraction theorem.

The ordinary Hilbert polynomial and the height-one condition on
the constructed P remain explicit geometric hypotheses. Their
identification with every curve supplied by the external covering
theorem, the integer affine-equation/fraction-field identification,
and the external uniform point counts remain open. This is the
confirmed proof improvement P1-MATH-0112; it does not claim the full
ordinary-curve exclusion or T1.7. Numbered coverage stays 79/167,
confirmed improvements become 112 and Palomar remains deferred.
Original manuscript bytes and compiler/dependency pins are unchanged.

Verified with Lean v4.36.0-rc2: full build 12515 jobs, direct axiom audit of 8917 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6864 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 14.84 GiB.


## Actual integer models, quotient-field equivalences and rational-plane radical-cover exclusion

The actual rational plane-curve presentation is now connected to
the integer plane/cover exclusion. A generic actual-localization
argument lifts an irreducible localized element to an irreducible
element of the original unique-factorization ring, up to actual
association. Applied to the two integer polynomial variables and
the explicit nonzero integer coefficient denominators, it constructs
an irreducible integer equation associated to any actual
irreducible rational plane equation. Its integer points agree
exactly, and its partial degrees are bounded by the rational
equation's corresponding partial degrees. No separately supplied
primitive integer model or coefficient-height estimate is used.

The actual localized prime-quotient fraction fields are proved
equivalent. The integer principal curve ideal maps to the rational
principal ideal, and the denominator set is proved disjoint from
the integer ideal because the rational ideal is proper. The
constructed integer/rational function-field equivalence preserves
every literal specialized integer polynomial. In particular square
status and the actual scaled radical functions are transported.

An explicit base-field equivalence transports the actual extension
algebra, preserves its actual finrank exactly, and preserves finite
dimension. The literal radical roots in the supplied rational-
curve extension therefore give the literal radical roots over the
constructed integer model, with exactly the same degree bound.
The final theorem chooses a single critical-band threshold before
the rational plane equation, all its coefficients, its actual
finite extension, radical roots and integer coefficients, offsets,
root-family cardinality and integer host. It excludes all admissible
comparable hosts under the explicit rational partial-degree and
actual finite-cover-degree bounds, including constant-coordinate
images and even cover degrees. Every model and scalar transport in
this rational-to-integer bridge is constructed internally.

This extends P1-MATH-0111 and P1-MATH-0112. Still open are the
actual projective-source/affine-curve field identification for the
extracted plane equation, its affine irreducibility and degree
comparison through the chosen chart, the ordinary geometric
curve-to-height-one/Hilbert identification, and the external
uniform counting inputs. T1.7 stays in_progress, numbered coverage
stays 79/167, confirmed improvements stay 112 and Palomar remains
deferred. Original manuscript bytes and pins are unchanged.

Verified with Lean v4.36.0-rc2: full build 12531 jobs, direct axiom audit of 8941 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6896 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 14.82 GiB.


## Actual homogeneous charts, constructed projective field covers and source-curve exclusion

The alternative Step 5--6 exclusion is now proved on the actual
projective radical source, with no supplied affine presentation,
extension field, cover-degree bound or literal radical roots.
For a homogeneous irreducible plane equation, its actual nonempty
Z-chart quotient is constructed and proved a domain. Its literal
affine specialization is nonzero and irreducible. Both actual
affine partial degrees are bounded by the homogeneous degree;
the proof uses the actual coefficient specialization and variable
swap, with no coefficient-height hypothesis.

A generic finite graded projection and actual chart equivalence
construct a finite extension of the actual chart fraction field.
The extension carrier is the actual projective source function
field. Its degree is proved equal to the actual graded module
rank, and the supplied homogeneous quadratic relations construct
the literal roots in that field. Applying this to the actual
source prime quotient and actual native Veronese chart transports
every actual radical polynomial to the actual affine curve
quotient, not merely its abstract square class.

For an actual height-one projective source point with Hilbert
multiplicity at most D*E, its own irreducible homogeneous plane
equation is extracted and its plane degree and actual source cover
rank are at most E. Actual containment of the affine image ideal
in the host evaluation kernel proves the Z-chart nonempty, the
extracted equation not at infinity, and the literal affine host
equation. Thus all hypotheses of the rational-plane radical-cover
exclusion are derived from the actual source data.

The final theorem chooses a single critical-band threshold before
the actual radical-source equations and nonzero integer
coefficients, D, offsets, projective point, curve-height proof,
Hilbert bound, offset family degree and integer host. It excludes
all admissible comparable hosts on every actual height-one source
curve of Hilbert multiplicity <=D*E when k>=4(E+1)^2. Constant-
coordinate images and all finite cover degrees are included.
No genus, Riemann--Hurwitz, assumed graph, supplied affine equation,
supplied field presentation, assumed cover rank or supplied radical
root is a premise of this final actual-source statement.

This extends P1-MATH-0111 and P1-MATH-0112. The ordinary geometric
curve-to-height-one/Hilbert identification and the external uniform
surface and curve point counts remain open. The ordinary quotient
comparison has already been proved separately, and its final host
and multiplicity composition with this source theorem remains to
be completed. T1.7 stays in_progress; numbered coverage stays 79/167,
confirmed improvements stay 112 and Palomar remains deferred.
Original manuscript bytes and compiler/dependency pins are unchanged.

Verified with Lean v4.36.0-rc2: full build 12545 jobs, direct axiom audit of 8960 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6920 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 14.79 GiB.


## Actual ordinary host and Hilbert comparison complete the source exclusion

The actual ordinary prime quotient now supplies the complete
input to the actual projective-source exclusion. Its ordinary
Hilbert polynomial E*n+beta bounds the induced source Hilbert
multiplicity by D*E, using the actual graded injection and the
actual plane-degree times cover-rank comparison. An actual
ordinary affine host evaluation, with Z=1 and Q in its kernel,
proves the source Z-coordinate nonzero and the actual source
image ideal contained in the host kernel.

The final ordinary-curve theorem chooses its critical-band
threshold before all radical equations, integer coefficients,
ordinary prime ideals, Hilbert constant terms and hosts. For
k>=4(E+1)^2 it excludes every admissible comparable host under
the explicit induced source-height-one and actual ordinary
linear-Hilbert hypotheses. It internally constructs the source
point, source degree cap, image containment, irreducible affine
equation and actual projective function-field radical cover.
Both constant-coordinate cases and all finite cover degrees
are included. No supplied source point, affine presentation,
cover, roots, degree cap or genus premise remains.

This completes the previously open ordinary host/multiplicity
composition in P1-MATH-0111 and P1-MATH-0112. The general geometric
curve-to-induced-source-height-one and ordinary linear-Hilbert
identification, and external uniform surface/curve counting
inputs, remain open. T1.7 stays in_progress, numbered coverage
stays 79/167, confirmed improvements stay 112 and Palomar remains
deferred. Original manuscript bytes and pinned dependencies are
unchanged.

Verified with Lean v4.36.0-rc2: full build 12551 jobs, direct axiom audit of 8964 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6924 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 14.77 GiB.


## Actual inverse homogenization and ordinary/source quotient chart isomorphism

The actual ordinary and weighted radical equations are proved
to define exactly the same quotient after Z=1. The two defining
ideals plus the literal ideal (Z-1) are equal. The forward weighted
substitution is the identity after every Z=1 ring evaluation.

The literal inverse homogenization sends each base variable V
to Z^(D-1)*V and leaves each radical variable unchanged. It sends
ordinary homogeneous degree n to weighted degree D*n. Composing
with the forward substitution multiplies an actual homogeneous
ordinary polynomial by Z^((D-1)*n). The inverse homogenization
is also the identity after every Z=1 evaluation.

For every actual homogeneous ordinary ideal containing the radical
relations, its induced source quotient and its ordinary quotient
now have an explicitly constructed isomorphism of their actual
Z-coordinate charts. The map is the actual coordinate map on
dehomogenized elements; its inverse is built from the literal
inverse homogenization. Injectivity clears powers of Z using the
actual quotient-to-ordinary injection. No primality, domain,
dimension, curve-height, Hilbert or nonzero-coordinate premise
is required for this chart isomorphism. It includes nonreduced
quotients and empty charts.

This strengthens the ordinary-to-source identification supporting
P1-MATH-0112. It does not yet prove equality of ambient prime
heights: the full localized ambient-ring comparison and its prime
height transport remain to be established. The geometric linear
Hilbert identification and external uniform counting inputs also
remain open. T1.7 stays in_progress; numbered coverage stays
79/167, confirmed improvements stay 112 and Palomar is deferred.
Original manuscript bytes and pinned dependencies are unchanged.

Verified with Lean v4.36.0-rc2: full build 12559 jobs, direct axiom audit of 8986 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6961 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 14.76 GiB.


## Actual ambient ordinary/source height equality and surface-curve exclusion

The ambient ordinary-to-source prime-height comparison is now
proved. A generic bijective homogeneous coordinate chart map
induces a bijection on the full localized rings, including rings
with zero divisors. The proof clears denominators of actual
homogeneous components. This comparison persists in every
positive Veronese ring: the clearing exponent is made divisible
by D while preserving the actual homogeneous preimage degree.
An actual ring isomorphism after inverting a coordinate preserves
the heights of all primes meeting that chart.

The actual ordinary radical surface is the quotient by the
literal ordinary radical relations. Its grading is constructed.
Equality of the weighted and ordinary defining ideals after
Z=1 proves that the actual forward coordinate map on the two
ambient charts is bijective. The generic localization and
Veronese results therefore apply to the actual ambient map,
not only to the previously compared curve quotients.

For an actual homogeneous ordinary prime Q containing the
radical relations, the prime in the actual ordinary surface
Veronese ring is constructed as the kernel of its actual curve
evaluation quotient map. Its contraction is proved equal to the
previously constructed source ideal. Whenever Z is outside Q,
the two actual ambient prime heights are equal.

The final uniform ordinary-surface-curve exclusion now assumes
height one only of the prime in the actual ordinary radical
surface. Height one of the induced source is derived internally.
Its actual ordinary Hilbert polynomial E*n+beta bounds all
required source, plane and cover degrees. The final statement
supplies neither an induced source-height hypothesis nor a
source point, affine equation, cover field, root or cover bound.
Its threshold is uniform before all actual ideals, equations,
integer coefficients and hosts. All coordinate cases and finite
cover degrees are included.

This closes the algebraic ambient height bridge in P1-MATH-0112
and strengthens the exclusion recorded in P1-MATH-0111. The
identification of exceptional curves from a geometric uniform
covering theorem with these actual prime/Hilbert data, and the
external uniform covering and point-counting inputs, remain
open. T1.7 stays in_progress; numbered coverage remains 79/167,
confirmed improvements remain 112 and Palomar is deferred.
Original manuscript bytes and pinned dependencies are unchanged.

Verified with Lean v4.36.0-rc2: full build 12575 jobs, direct axiom audit of 9012 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 6996 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 14.74 GiB.


## Actual simultaneous degree gap and conditional ordinary surface point counts

One coefficient-uniform critical threshold now excludes all
ordinary degrees up to a chosen cap E simultaneously. The actual
Hilbert slope e is arbitrary: every actual ordinary surface curve
through an admissible host has e>E. This follows from the actual
source multiplicity bound D*e and the previously proved uniform
source exclusion with cap E.

Normalized integral points are actual integer coordinate functions
on Fin 3 plus the radical indices, with Z=1. Their bounded box
and their actual ideal-kernel point subsets are finite sets.
Projection gives the integer host (X,Y); chosen literal radical
lifts inject hosts into the point set. An actual curve record
contains its prime homogeneous ideal, literal relations, actual
ordinary surface height one, positive degree and actual linear
Hilbert polynomial. The degree is proved unique for its ideal.

The geometric counting inputs are isolated as two unproved
properties, always explicit theorem arguments. The uniform curve
input bounds the actual normalized integer-point set by
A*H^(1/e+delta), uniformly over bounded ambient dimensions and
bounded actual degrees. Its literature source is
[Pila, Theorem A, Astérisque 228 (1995), pp. 183--187](https://www.numdam.org/item/AST_1995__228__183_0.pdf).
The uniform lifted-surface input produces actual finite exception
sets and actual ordinary curve records of bounded degree. Its
curve-number and exception exponents are 1/sqrt(2^k)+delta and
2/sqrt(2^k)+delta. It includes the unproved finite-projection
lifting and prime/Hilbert presentation needed to apply
[Salberger, arXiv:2311.05561v1, Lemma 2](https://arxiv.org/pdf/2311.05561v1).
Neither property is an axiom or a proved external counting theorem.

Given an actual finite covering of admissible point sets, the
proved degree gap discards every curve of degree <=E. The explicit
curve input bounds the remaining contributions by
#exceptions + #curves*A*H^(1/(E+1)+delta). Fixed choices of E, k
and delta are constructed before N so that both surface-cover
exponents, after the polynomial height H<=B0*N^q, are <=epsilon/2.

The resulting theorem proves N^epsilon bounds for the actual
normalized point sets and their actual projected integer hosts,
conditional only on the two stated uniform geometric properties.
It chooses the equation threshold before the ambient-size cap,
then its count constant and critical cutoff before all actual
equations, coefficients, offsets, point sets and heights. The
finite coverings, degree cut and actual point counts are composed;
the desired N^epsilon host bound is never an input.

The external properties themselves and their geometric translation
remain unproved. The literal dyadic square-equation host/height
composition, the general N^(1/2+epsilon) geometric bound and the
remaining graph consequences of T1.7 still need to be completed.
T1.7 stays in_progress; numbered coverage remains 79/167, confirmed
improvements remain 112 and Palomar is deferred. Original manuscript
bytes and pinned dependencies are unchanged.

Verified with Lean v4.36.0-rc2: full build 12593 jobs, direct axiom audit of 9032 theorem/lemma declarations using only propext, Classical.choice and Quot.sound, and 7026 distinct ledger declaration references. Source integrity: 138 manifest entries and all 167 numbered results. Ubuntu root free space 14.70 GiB.
