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


## Literal integer square-equation hosts and equation-count-independent height

The literal integer square-equation host and point-height
composition is now proved. Evaluating the actual native linear
products and ordinary radical relations at (Y,X,Z,w)=(y,x,1,w)
gives exactly the original integer split-product equations.
Their integer roots therefore put the literal lift in the actual
ordinary radical surface ideal kernel.

For fixed D>=1 with A0+K<=2D, every ordinary coordinate of a
literal dyadic root lift is bounded by
(2^D+3^K)*N^D. This height constant is independent of the number
of equations. It uses the individual radical bounds rather than
the larger common constant needed for the sum-of-radicals
projection. The natural floor of this real height is proved >=1,
no larger than the real height, and contains the actual integer
lift in the actual finite normalized point set.

The final theorem starts with arbitrary nonzero integer
coefficients of height <=N^A0, disjoint offset sets of common
positive size a and distinct singleton offsets on the Y side.
It counts an arbitrary finite set of actual integer hosts for
which the literal square equations have integer roots. The hosts
have X in the dyadic range, |Y|<=2N, positive selected values,
an injective actual left even-selection map and actual left/right
square-class images in direct sum. The offset cap is any fixed
polynomial in the critical logarithmic window.

The proof derives the offset bound <=N from the critical scale,
constructs a choice of literal integer roots for each host, lifts
the actual host set to the actual bounded ordinary point set,
and proves that projection recovers exactly the original host
set. The preceding conditional point-count theorem then gives
the coefficient-uniform A*N^epsilon host bound. The equation
threshold is chosen before the ambient-size cap, and A and the
N cutoff before every actual system, coefficient and host set.
Choosing a suitable fixed D from A0 and K is also proved.

Only the two previously isolated uniform geometric properties
remain explicit unproved arguments in this literal per-system
degree-(a,1) result. No abstract host-count or point-height
conclusion is a premise. Coefficient smoothness is not used and
coefficient enumeration is not included. The general half-power
geometric bound, the graph applications with their own alignment
scope, and the external geometric input proofs remain open.
T1.7 stays in_progress; numbered coverage remains 79/167,
confirmed improvements remain 112 and Palomar is deferred.
Original manuscript bytes and pinned dependencies are unchanged.

Verified under Lean v4.36.0-rc2: full build passed (12599 jobs); direct axiom audit passed for 9043 declarations using only propext, Classical.choice and Quot.sound; all 7039 distinct ledger/evidence declaration references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.68 GiB.


## Repeated left offsets remove host independence from the conditional count

For every fixed left size a>=2, the literal degree-(a,1)
coefficient-uniform N^epsilon host bound now requires no actual
square-class independence or direct-sum hypothesis on the host.
The two explicit unproved uniform geometric properties remain
arguments, with precisely the same quantifier order and scope.

The strengthened terminal graph argument first proves an
independence-free alternative: an integral point on a reduced
rational graph selected by a bounded offset grid either has the
existing offset-only bound, or the entire rational graph is an
actual affine line. For the latter alternative, one good family
contains two distinct left roots with the same right root.
Their affine equations force slope zero. The actual host would
then satisfy Y+j=0, contrary to positivity. Neither the actual
left even-selection map nor the actual left/right class spaces
is used in this contradiction.

This repeated-left argument is composed through the actual
integer and rational plane covers, including constant-coordinate
images, the actual projective source curve, ambient prime height,
ordinary Hilbert multiplicity and the simultaneous ordinary
degree gap. It then supplies the actual finite curve-cover count,
conditional surface point count and literal integer-root host
count with admissibility consisting only of the dyadic bounds
and positivity of the selected values. The proof covers even
finite radical-cover degrees and arbitrary nonzero integer
coefficients of bounded polynomial height. It does not assume
coefficient smoothness or include pattern enumeration.

This recovers the independence-free per-system scope needed
for the a>=2 part of the second graph consequence in T1.7.
The a=1 case with geometric nonalignment, the general half-power
bound, smooth coefficient-pattern enumeration and the two
external uniform geometric proofs remain open. T1.7 stays
in_progress; numbered coverage remains 79/167 and confirmed
mathematical improvements remain 112. This is a proof improvement,
not a confirmed manuscript-conclusion error. Palomar is deferred;
the original manuscript bytes and pinned dependencies are unchanged.

Verified under Lean v4.36.0-rc2: full build passed (12619 jobs); direct axiom audit passed for 9053 declarations using only propext, Classical.choice and Quot.sound; all 7051 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.64 GiB.


## The affine exception gives the actual source alignment

The positive-left-size degree-(a,1) host count now has an
independence-free nonaligned version, including a=1. It uses
actual integer hosts with both coordinates in the positive
dyadic range and excludes only a concrete bounded positive
coprime alignment. No even-selection injectivity or left/right
square-class directness is assumed.

The affine exceptional graph is handled constructively. Two
distinct bounded integer grid points and the actual host on the
same rational affine graph give an exact rational cross-product
identity, then its exact integer counterpart. The existing
bounded collinearity argument constructs positive coprime a,b
with a,b<=2B and |bX-aY|<=(a+b)B. The critical-window cutoff
ensures that both host coordinates exceed the offset cap B.
This discharges the affine alternative for every positive common
left size; the other graph cases retain the same offset-only
polynomial bound.

For the paper's offset cap B=L+1 and L>=1, the constructed
alignment is proved to imply the literal
CompressedTargetAlignment.Aligned 1 X.natAbs Y.natAbs L.
The final source_uniform_hosts theorem therefore assumes the
paper's actual nonalignment predicate, rather than a supplied
line-exclusion or graph-bound conclusion.

The argument is composed through the actual integer/rational
plane covers, projective source, ambient prime height and
ordinary Hilbert multiplicity, simultaneous degree gap, actual
finite curve-cover count, conditional surface point count and
literal integer-root lift. One cutoff is uniform before all
actual equations, coefficients, curves, covers and hosts.
The two previously isolated uniform geometric properties remain
explicit unproved arguments; the host-count target is not a
premise. Constant-coordinate images and even finite cover
degrees remain included.

Together with the repeated-left a>=2 version, this recovers
the per-system alignment scope needed by the second graph
consequence of T1.7. Smooth coefficient-pattern enumeration,
the general half-power geometric bound, and the external
uniform geometric proofs remain open. T1.7 stays in_progress,
numbered coverage remains 79/167, confirmed improvements remain
112, and Palomar is deferred. This is a proof improvement,
not a confirmed manuscript-conclusion error. Original manuscript
bytes and pinned dependencies are unchanged.

Verified under Lean v4.36.0-rc2: full build passed (12639 jobs); direct axiom audit passed for 9067 declarations using only propext, Classical.choice and Quot.sound; all 7069 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.60 GiB.


## Direct integer systems and a uniform fixed-subsystem reduction

The literal degree-(a,1) per-system host bound now has a
single direct statement with exactly the paper's alignment
scope. It starts only with finite integer systems d_i,I_i,j_i,
common positive left size a, disjoint left root sets, distinct
right offsets, coefficients of height <=N^A0, offsets <=L+1,
positive dyadic hosts and actual integer roots of
w_i^2=d_i*product_(z in I_i)(X+z)*(Y+j_i).
For a>=2 aligned hosts are permitted; only when a=1 does the
statement exclude the actual source alignment predicate.
Neither host square-class injectivity nor directness is assumed.

The proof chooses the homogenization degree from A0,K,
constructs the actual homogeneous radicand list and its index
equivalence, and constructs both selected-value sets. Positivity
of all selected values and L>=1 are deduced uniformly from the
critical scale and offset bounds. They are no longer supplied
premises. The two alignment cases share one equation threshold,
one host constant and one scale cutoff.

The stronger uniform_hosts_of_many statement selects the first
k equations from every larger finite system. Its host constant
and cutoff are therefore independent of the actual number of
equations. The two explicit unproved uniform geometric input
properties are needed only at the chosen fixed equation count
k, with arbitrary curve degree cap for the curve-count property.
The equation threshold is chosen before these properties; the
host constant and scale cutoff precede every actual system,
coefficient and finite host set. There is no supplied homogeneous
list, projective curve, field, cover, Hilbert polynomial,
height bound or target count in the final statement.

Only the two isolated uniform geometric properties remain
unproved explicit arguments in this direct per-system theorem.
Coefficient smoothness is unnecessary; summing smooth patterns,
the actual graph component-to-system reduction, the general
half-power bound and the external geometric proofs remain open.
T1.7 stays in_progress; numbered coverage remains 79/167 and
confirmed improvements remain 112. This strengthens the proof,
without a confirmed manuscript-conclusion error. Palomar is
deferred; original manuscript bytes and dependencies are unchanged.

Verified under Lean v4.36.0-rc2: full build passed (12643 jobs); direct axiom audit passed for 9072 declarations using only propext, Classical.choice and Quot.sound; all 7076 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.58 GiB.


## Actual smooth-pattern summation for degree-one systems

The actual offset and smooth coefficient-pattern summation
for degree-(a,1) systems is now proved. The finite pool consists
of k bounded-cardinality subsets of the integer offset interval,
k right offsets, and k subsets of the literal primes <=H.
Each coefficient is the positive product of its actual prime
support. Pool membership, positivity, offset bounds and the
coefficient bound <=4^H are proved directly.

The offset-pattern count is at most
(((K+1)*4^K*3)^k)*(L+1)^((K+1)*k).
The existing elementary Chebyshev support bound gives at most
N^epsilon prime-support patterns for every fixed k and every
H<=D*(L+1) in the critical band. Combining these proves the
unconditional N^epsilon bound for the entire actual finite pool.
No PNT assumption or new external estimate is used.
A fixed polynomial coefficient-height exponent is constructed
from D and the critical-band constant, uniformly before all
N,L,H,k,K and every actual support pattern.

SmoothDegreeOneHostCount.uniform_hosts sums the literal integer
host counts over the valid actual patterns. It chooses one fixed
k, then takes the two explicit unproved uniform geometric
properties only at that k. The constant and scale cutoff precede
a, N,L,H, every actual pattern and every finite host set. A host
need only admit some valid smooth split-product square system;
the witness pattern may vary with the host. Disjoint left sets,
distinct right offsets, common positive left size, actual integer
roots and the dyadic host bounds are checked in that witness.
Aligned hosts are permitted for a>=2; for a=1 only the literal
source alignment is excluded. No host independence or direct-sum
hypothesis is present, and no target count is a premise.

This closes the explicit smooth-pattern summation in the second
T1.7 graph consequence, conditional only on the two isolated
uniform geometric inputs. Extraction of these actual systems
from the literal graph components, the general half-power bound
and the external geometric proofs remain open. T1.7 stays
in_progress; numbered coverage remains 79/167 and confirmed
improvements remain 112. This is a proof improvement without a
confirmed manuscript-conclusion error. Palomar is deferred;
original manuscript bytes and pinned dependencies are unchanged.

Verified under Lean v4.36.0-rc2: full build passed (12649 jobs); direct axiom audit passed for 9085 declarations using only propext, Classical.choice and Quot.sound; all 7097 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.57 GiB.


## Actual degree-one graph components construct the counted integer systems

The literal two-window graph component-to-system extraction
is now proved. The graph is the actual largePrimeGraph with
cutoff 10*(L+1), and unpinned means the actual ComponentPinned
predicate. Its component indicator is proved to satisfy the
actual large-prime equations. The component product therefore
has no odd prime support above the cutoff. Its actual support
product is a positive smooth coefficient giving an integer
square prescription.

The component's two sets of integer offsets are constructed
from its literal left/right vertices using u.val-1. Their
cardinalities equal the actual numbers of vertices in each
window. Distinct components give disjoint offset sets on each
side. The actual component product is proved to be exactly
the product of the two offset polynomials at the actual starts.
When the right side has one vertex, this yields the literal
integer square equation with an actual integer root.

An injective choice of k actual unpinned components with left
size a and right size one constructs the full valid smooth
pattern witness. Selection from the actual finite component
set is proved internally; no system-extraction premise is used.
DegreeOneGraphHostCount.uniform_hosts then proves the actual
N^epsilon dyadic host bound, conditional only on the two explicit
uniform geometric properties at a fixed k. It assumes no actual
square-class independence, directness, supplied coefficient
height, square roots, curve, field or abstract host-count bound.
For a>=2 aligned hosts are included; for a=1 only the actual
source alignment is excluded.

The two ordered windows are both counted explicitly. The source
alignment is proved symmetric. A second theorem counts either
window order, and a pigeonhole version accepts a total of at
least 2k typed components across those two orders. All constants
and cutoffs precede actual dyadic starts, window lengths,
components and finite host sets. Formal vertex copies are kept
when the physical windows overlap.

This completes the actual degree-(a,1) graph-count composition
under the two isolated uniform geometric inputs, including the
previously proved finite smooth-pattern enumeration. The general
half-power geometric count and the proofs of the two external
uniform geometric inputs remain open. T1.7 stays in_progress;
numbered coverage remains 79/167 and confirmed improvements
remain 112. This is a proof improvement without a confirmed
manuscript-conclusion error. Palomar is deferred; original
manuscript bytes and pinned dependencies are unchanged.

Verified under Lean v4.36.0-rc2: full build passed (12657 jobs); direct axiom audit passed for 9109 declarations using only propext, Classical.choice and Quot.sound; all 7127 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.55 GiB.


## Literal integer points in the chosen weighted-source embedding

The general split-product integer-root system now constructs
an actual point of the weighted source and of its chosen
projective coordinate embedding. The construction permits
arbitrary disjoint nonempty left and right root sets; it is
not restricted to singleton right sets.

Literal integer square equations annihilate the actual weighted
relation ideal at Z=1. Quotient evaluation and its restriction
to the actual source Veronese are constructed. The chosen
projective generator index is identified with the actual degree-D
base monomials plus radical variables. Their point coordinates
are the literal integers X^u*Y^v and w_i. Polynomial evaluation
at those integers is proved equal to the actual source evaluation
composed with the chosen embedding presentation.

The Z^D coordinate is proved to be one. The X*Z^(D-1) and
Y*Z^(D-1) coordinates recover the exact original integer host.
The actual finite bounded normalized coordinate point sets and
their ideal-kernel membership characterization are constructed.
Every literal coordinate is bounded by (2^D+3^K)*N^D; this
constant is independent of the equation count. The floor of
this real height is proved >=1 and contains the actual point.

Embedded curve-ideal containment is proved equivalent to actual
source-ideal containment, using surjectivity of the actual
embedding presentation. It supplies the actual affine plane
host-image kernel. Thus the already proved source low-degree
exclusion applies directly to the literal embedded integer point
and gives chosen-coordinate Hilbert multiplicity at least 2D.
This includes constant-coordinate images, with both actual
selected-set even-selection maps injective and their actual
images in direct sum. No host-image or degree-bound conclusion
is assumed in this new point-containment composition.

These are unconditional algebraic and height bridges for the
general half-power count. That count itself remains open: its
finite surface-cover and uniform curve-count applications must
be made in this chosen weighted-source embedding, with their
exact uniformity. The two previously isolated ordinary-embedding
input properties alone have not been asserted to cover this
new setting. The degree-(a,1) graph composition remains proved
under those two explicit ordinary geometric inputs. T1.7 stays
in_progress; numbered coverage remains 79/167, confirmed
improvements remain 112 and Palomar is deferred. No manuscript
conclusion error is confirmed; source bytes and dependencies
are unchanged.

Verified under Lean v4.36.0-rc2: full build passed (12667 jobs); direct axiom audit passed for 9127 declarations using only propext, Classical.choice and Quot.sound; all 7154 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.53 GiB.


## One generic curve input and the actual source finite-cover count

A single explicit generic curve-count property now covers
both actual ordinary curves and actual curves in the chosen
weighted-source embedding. Its input data are a homogeneous
prime ideal, a positive rational degree, the actual linear
Hilbert polynomial, a normalized coordinate chart and an
integer height box. The ambient coordinate count and degree cap
are fixed before all curves, coefficients, charts and heights.

This generic UniformNormalizedCurvePointCount.UniformBound is
an UNPROVED ARGUMENT, not an axiom or a newly proved version of
Pila. It includes the primary curve theorem and its translation
to actual prime/Hilbert data, non-geometrically-integral curves
over Q and the normalized chart, including the height-one case.
Primary sources are Pila, Theorem A, Astérisque 228 (1995),
https://www.numdam.org/item/AST_1995__228__183_0.pdf , and the
integral projective curve formulation in P3 in Salberger,
https://arxiv.org/pdf/2311.05561v1 , Lemma 3. The higher-dimensional
ambient/prime-presentation translation is not claimed proved.

The specialization of this one property to the previous actual
ordinary curve-count property is proved. Its specialization to
the actual chosen source-embedding point sets is also proved.
The two applications are therefore derived from a single generic
curve input, rather than silently identifying incompatible
embeddings or introducing an unexplained new source count.

To construct the source curve data, actual finite graded module
rank gives the actual source Hilbert slope. Existence of its
Hilbert polynomial then gives an actual affine polynomial with
slope equal to its actual multiplicity. This is transported to
the chosen embedding by equality of actual piece dimensions.
The resulting chosen-coordinate degree is proved positive for
every actual height-one source projective curve. No degree,
Hilbert polynomial or positivity assumption is added to that
curve data: they are constructed from the actual point and its
height-one property.

SourceCurvePointCover.finite_cover_bound now counts literal
integer hosts from an actual finite collection of such curves.
Every curve meeting a covered admissible literal root point has
actual degree at least 2D, by the proved source-degree bridge.
Filtering to these curves and applying the generic curve input
gives #hosts <= #exceptional_points + #curves*A*H^(1/(2D)+delta).
Exact host recovery proves injectivity of the actual lift.
Both selected-set even-selection injectivities and their actual
direct sum remain explicit in this general source argument.

The covering collection and its exceptional set are actual data
in this intermediate theorem; a surface-cover theorem is not
assumed proved. The final general half-power estimate still
requires a uniform surface-cover application in the chosen
source embedding and the numerical/height composition. The
primary geometric input proofs remain open. The degree-(a,1)
graph composition remains valid under its explicit curve and
ordinary surface-cover inputs. T1.7 stays in_progress; numbered
coverage remains 79/167, confirmed improvements remain 112,
and Palomar is deferred. No manuscript-conclusion error is
confirmed; original source bytes and dependencies are unchanged.

Verified under Lean v4.36.0-rc2: full build passed (12683 jobs); direct axiom audit passed for 9144 declarations using only propext, Classical.choice and Quot.sound; all 7183 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.50 GiB.


## The general literal half-power composition under its exact geometric inputs

The general coefficient-uniform N^(1/2+epsilon) literal
integer host count is now proved under two explicit geometric
properties: the generic normalized curve-count property and a
new chosen-source uniform surface-cover property. The latter
is an UNPROVED ARGUMENT, not an axiom or an asserted Salberger
theorem. It includes the primary P3 surface covering and the
bounded projection, lifting, geometric-integrality, degree and
actual prime/Hilbert presentation translation for this chosen
higher-dimensional weighted-source embedding. It is kept
distinct from the previous ordinary-embedding cover property.
Its data are an actual finite exceptional point set and actual
height-one source curves of bounded degree; the desired host
count is not part of the property.

The proof constructs literal root lifts in the actual normalized
source point set, with height floor((2^D+3^K)*N^D), and proves
that they annihilate the actual global embedding ideal. The
actual source cover yields finite exceptional points and curves.
Every curve meeting a covered admissible host has actual chosen
coordinate degree at least 2D. The proved finite-cover count
therefore gives curve exponent 1/(2D)+delta. Choosing k large
and delta small before the systems makes the covering decay
and height conversion yield N^(1/2+epsilon). All numerical
exponent choices and cardinality compositions are proved.

GeneralRootHostCount.uniform_hosts constructs D and the actual
homogeneous radicand list directly from the raw integer data.
The stronger uniform_hosts_of_many selects a fixed first k
equations from every larger finite system. The constant and
scale cutoff are independent of the actual equation count and
precede every coefficient, root set and finite host set. Only
the geometric properties at that fixed k and chosen D are used.
The root sets on both sides may have different positive sizes;
only their common total-degree cap K is used. No equal-degree
pigeonhole assumption is needed. Coefficients are arbitrary
nonzero integers of height <=N^A0; smoothness is unnecessary.
Offsets may lie in any fixed polynomial enlargement of the
critical window. The actual two selected-set even-selection
maps, their direct sum and positivity are explicit host
hypotheses, as in the general per-system manuscript assertion.
No homogeneous list, height, source point, curve, field, degree
bound or target host count is supplied in the final statement.

The per-system general half-power composition is therefore
closed under its exact generic-curve and chosen-source-cover
arguments. The degree-(a,1) and actual graph compositions retain
their stronger proved N^epsilon bounds under the generic curve
input and the distinct ordinary surface-cover input. The
primary geometric input proofs and the remaining full graph
consequence of the general half-power estimate remain open.
T1.7 stays in_progress; numbered coverage remains 79/167,
confirmed improvements remain 112 and Palomar is deferred.
This is a proof improvement without a confirmed manuscript
conclusion error; source bytes and dependencies are unchanged.

Verified under Lean v4.36.0-rc2: full build passed (12693 jobs); direct axiom audit passed for 9151 declarations using only propext, Classical.choice and Quot.sound; all 7193 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.48 GiB.


## General nonaligned literal hosts and the actual degree gap

The general nonaligned half-power composition is now proved
without either actual even-selection injectivity or the direct-sum
hypothesis. The proof excludes the actual source curves of degree D
using precisely the source's geometric nonalignment alternative.
Two functional square equations with disjoint nonempty left root
sets match two distinct integer roots to right roots. Their two
bounded grid points and the actual host lie on the same rational
affine graph. The previously proved exact grid-alignment theorem
constructs positive coprime slope data with the required bound.
A vertical degree-one image is impossible already from one
nonempty right root set: square matching forces X+i=0, contrary
to the far-positive host and bounded offsets. No square-class
independence premise enters either argument.

The actual height-one source curve small-degree theorem and
Hilbert multiplicity comparison now yield degree >=2D through
every such nonaligned integer root lift. A separately proved
finite-cover lemma accepts only a per-curve degree lower bound,
then performs the actual point lifting, injectivity, exceptional
set and finite curve cardinality composition. It does not assume
a host count. Substitution of the proved nonalignment degree gap
and the existing height/exponent calculations gives the full
general N^(1/2+epsilon) coefficient-uniform host count.

GeneralNonalignedRootHostCount constructs the homogeneous data
and selects a fixed subsystem, with constants independent of the
larger equation count. Its source_uniform_hosts_of_many starts
from literal dyadic integer hosts and the paper's exact
CompressedTargetAlignment.Aligned 1 nonalignment condition.
Critical-window positivity and the offset-to-scale comparison
are derived internally. The two root-set sizes can vary freely
subject to positivity and the common total-degree cap. Both
families are disjoint as required by the source-cover property.
There are no supplied fields, curves, Hilbert degrees, heights,
square-class maps, direct-sum facts or target count bounds.

The exact unproved inputs remain the generic normalized curve
count and chosen-source uniform surface-cover properties, each
explicit theorem arguments. Neither primary determinant theorem
nor its chosen-embedding translation is claimed proved. The
general actual graph population count and these geometric inputs
remain open. T1.7 stays in_progress, coverage remains 79/167,
confirmed improvements remain 112 and Palomar is deferred.
This verifies the source's nonalignment alternative and introduces
no new confirmed manuscript-conclusion error or source change.

Verified under Lean v4.36.0-rc2: full build passed (12705 jobs); direct axiom audit passed for 9161 declarations using only propext, Classical.choice and Quot.sound; all 7203 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.45 GiB.


## The actual general graph half-power consequence

The first actual graph consequence of companion T1.7 is now
proved under exactly the generic normalized curve-count and
chosen-source uniform surface-cover properties. For every fixed
eta,epsilon>0, actual dyadic pairs with literal source nonalignment
and at least eta*(L+1) nontrivial unpinned components have
O(N^(1/2+epsilon)) hosts. The graph and component count are the
paper's actual arithmetic objects. The theorem even includes
overlapping physical windows; the two indexed copies of their
vertices are retained throughout. No component, polynomial
system, degree lower bound or target host count is assumed.

The construction enumerates bounded root subsets on BOTH sides,
including unequal positive sizes. Its exact finite pool consists
of two families of bounded offset sets and one family of actual
small-prime supports. Elementary Chebyshev bounds already proved
in the project give N^epsilon patterns, and the product of each
actual support has uniform polynomial coefficient height. No
prime-number theorem or smooth-number asymptotic is added.
The general nonaligned per-system estimate is summed over this
pool, with an explicit split of the epsilon margin.

Every actual nontrivial unpinned component meets both window
copies. Its two literal offset sets have total cardinality equal
to its vertex count; distinct components give disjoint root sets.
The product of the component labels has odd-prime support below
10*(L+1), and its actual squarefree prescription gives an integer
root for the corresponding equation. A chosen finite family of
components therefore constructs every pattern and root witness
required by the uniform smooth-system theorem.

For a population c>=eta*(L+1), the actual disjoint-vertex budget
and size cap ceil(4/eta) give at least eta*(L+1)/2 small components.
The logarithmic critical window eventually supplies any fixed
required number k. The fixed system size, chosen homogeneous
embedding degree, coefficient and pattern bounds all precede the
hosts and component choices. The final graph count is obtained
internally by injective host conversion and finite covering.

The first and degree-(a,1) graph consequences are thus composed
from the actual arithmetic graph under their respective explicit
geometric properties. The primary determinant theorems and their
translation/lifting statements remain unproved arguments; the
full T1.7 statement and later weighted sectors are not declared
complete. Coverage remains 79/167, confirmed improvements remain
112 and Palomar is deferred. No source bytes are changed and no
new error in a manuscript conclusion is confirmed.

Verified under Lean v4.36.0-rc2: full build passed (12715 jobs); direct axiom audit passed for 9183 declarations using only propext, Classical.choice and Quot.sound; all 7235 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.42 GiB.


## The actual dense weighted sector, conditional on the exact geometric properties

Companion T1.8, the dense weighted sector, now has its full
finite-sum and asymptotic composition under explicitly listed
geometric properties. Its status is CONDITIONAL, not proved.
For arbitrary actual dyadic host sets F, literal nonalignment and
c(x,y)>=eta*(L+1) imply sum_F(2^rho-1)=O(N^(1+epsilon)).
The same bound is proved for the full value kernel with the
separate block-parity equations omitted. In fact the theorem
bounds the larger sum_F 2^r where r is the actual dimension of
the kernel of the two-window value parity map, including local
relations. The effective pair nullity is proved <= this actual
full kernel rank. No compatibility, regularity or separation
hypothesis is needed, so overlapping physical windows are included.

The unconditional graph foundations are now literal. Swapping
the two start windows gives a graph isomorphism, a connected-
component equivalence and exact pin preservation. It exchanges
the two vertex projections. A general disjoint-block argument
proves 4*c<=2*B+2*t2+t3, and the actual component construction
identifies each size-two component with type (1,1). Every size-
three component has type (2,1), either in the original graph or
under the actual swap equivalence. The resulting cardinality
bounds justify the precise two-orientation split used by T1.8.

The actual raw value kernel is contained in the large-prime
solution space and therefore has dimension <=D_defect+c.
Previously proved critical defect estimates yield uniformly
D_defect=o(B). Exact binary-power conversion gives weight
<=N^(1+delta) globally and <=N^(1/2+delta) whenever the two-
and three-vertex populations are bounded. The proof partitions
the finite host set into many (1,1) components, many oriented
(2,1) components, and the remainder. The two subpower actual
graph counts bound the first populations, and the actual general
half-power graph count bounds the remainder. All partitions,
weights, epsilon margins, sums and constant orders are proved.

Only the exact generic normalized curve property and the
ordinary/chosen-source surface-cover properties remain inputs.
Their uses are limited to the fixed dimensions and degree caps
selected before the hosts. The generic property supplies the
ordinary Pila specialization internally. These properties still
include unproved primary determinant estimates and their exact
projection, lifting, integrality and prime/Hilbert translations.
No target weighted bound or arithmetic graph count is supplied
as an assumption. Thus T1.8 moves from not_started to conditional;
proved numbered coverage stays 79/167. T1.7 and the full papers
remain incomplete, confirmed improvements stay 112, and Palomar
is deferred. Original manuscript bytes are unchanged and no
manuscript-conclusion error is newly confirmed.

Verified under Lean v4.36.0-rc2: full build passed (12727 jobs); direct axiom audit passed for 9215 declarations using only propext, Classical.choice and Quot.sound; all 7271 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.38 GiB.


## Actual second-cumulant and two-channel approximations under the geometric inputs

The conditional geometric graph bounds are now connected to
the actual infinite-model second factorial cumulant. The dense
nonaligned coefficient family used by the existing pair-profile
reduction has absolute activity <=N^(-1+epsilon), uniformly in
the critical window, under the same explicit generic curve and
ordinary/chosen-source cover properties. Every actual pair in
this family has positive joint mass and relative nullity >L/10.
Raw-kernel domination and the unconditional defect bound imply
an actual nontrivial-component population >=(L+1)/100. Thus the
proved weighted graph sector applies to the precise family
remaining in the probabilistic reduction, not an assumed count.

A new exact finite identity converts any selected family of
two-element subsets to its actual ordered pair hosts, giving
exactly twice the original weighted sum. Literal source
nonalignment is recovered in both orientations from exclusion
of the actual aligned family. The compatible centered-moment
bound, positive exact marginals, dyadic marginal cap, full
kernel domination and finite weighted sum give the stated
dense-activity rate. No compatibility probability, marginal,
rank, host count or dense-activity estimate is supplied as an
extra theorem premise. All are recovered from the existing
actual model and membership in its defined dense family.

PairProfilesUnderGeometricInputs.uniform_profiles then proves
both |kappa2-2*beta|<=N^(-4/5+epsilon) and the exact two-channel
approximation with mainTerm(2,3)+mainTerm(3,4), for the actual
second factorial cumulant of the full dyadic count. Fixed
threshold multipliers satisfy the original 8*(L+1)<=H<=D*(L+1)
scope. The nonaligned dense remainder is completely eliminated
in these two conditional conclusions. The already proved aligned,
weak, irregular, diagonal and channel comparison estimates
supply all other terms, with explicit epsilon absorption.

The exact unproved inputs remain solely the generic normalized
curve and the two distinct surface-cover properties, at the
fixed dimensions/caps exposed before the hosts. In particular
this composition does not add a BCN or target-profile argument.
The raw positive/signed relation-count displays and the full
phase-asymptotic alignment in article Theorem 3.3 are not newly
claimed complete. That row stays in_progress. T1.8 remains
conditional; T1.7 and the whole project remain incomplete.
Proved numbered coverage stays 79/167 and confirmed improvements
stay 112. No source bytes, compiler or dependencies are changed;
Palomar remains deferred and no manuscript-conclusion error is
newly confirmed.

Verified under Lean v4.36.0-rc2: full build passed (12733 jobs); direct axiom audit passed for 9222 declarations using only propext, Classical.choice and Quot.sound; all 7279 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.36 GiB.


## The complete actual principal-edge input under the geometric properties

Article Corollary 3.4 now has all its actual principal-edge
inputs under the explicit geometric properties. Its ledger
status is CONDITIONAL, not proved. The new uniform_edge_input
packages one common set of geometric dimensions and caps,
positive beta comparison constants and one scale cutoff before
all windows and prime thresholds. It gives the exact edge-card
bound 26*(L+1)*N, beta comparable to L*N^(-2/3), the actual
second-cumulant comparison |kappa2-2*beta|<=N^(-4/5+epsilon),
and the actual ordered covariance sum outside these edges.
The per-channel actual rank, regularity and joint-mass caps
were already proved by CompatibleChannelEdges.edge_data;
these retain the separate denominators 3 and 4 and nominal
marginal (2^L)^(-1). Together they give the complete source
corollary, with a stronger remainder than its additional B/N.

The new finite argument uses the exact positive gap between
absolute pair activity and half the actual second factorial
cumulant, and the exact nonnegative beta-minus-edge-activity
gap. Subtracting the actual edge population from all two-element
subsets gives the off-edge absolute activity. The conditional
cumulant profile therefore bounds the whole off-edge activity
by N^(-4/5+epsilon). An exact ordered-host identity gives the
same rate for every subset G of the full dyadic ground set,
with no regularity or separation premise on that actual-
marginal statement.

For the original source formula, the regular-set marginal
identity is applied inside the actual Bochner integral.
regular_nominal_coefficient proves the coefficient is precisely
the expectation of (J_x-p)*(J_y-p), with p=(2^L)^(-1), rather
than leaving a change of centering implicit. The final ordered
sum is over the actual regular set and excludes exactly the
literal PrincipalChannelEdges.edges. Its bound is
N^(-4/5+epsilon), which also implies the printed bound with
an additional B/N term. All arithmetic, probability, centering,
set partitions, orientation factors and exponent absorption
are internally proved. The nominal covariance count is not
provided as a theorem argument.

The exact unproved inputs remain the generic normalized curve
property and the ordinary/chosen-source surface-cover properties
at the exposed fixed dimensions and caps. No BCN input, target
cumulant bound, covariance remainder or opaque arithmetic input
is added. Primary determinant/translation proofs remain open.
Main 3.4 moves from in_progress to conditional, T1.8 remains
conditional, main 3.3 and T1.7 remain in_progress, and proved
coverage stays 79/167. Confirmed improvements stay 112, original
source bytes are preserved, and Palomar remains deferred.
No new manuscript-conclusion error is confirmed.

Verified under Lean v4.36.0-rc2: full build passed (12735 jobs); direct axiom audit passed for 9226 declarations using only propext, Classical.choice and Quot.sound; all 7283 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.35 GiB.


## The literal full arithmetic rank and a stronger conditional residual

The literal arithmetic rank in the manuscript is now connected
explicitly to the full value-kernel bound. It is pairLoss=2L minus
the dimension of the joint square-class image, INCLUDING local
kernels, whereas the exact-marginal probabilistic development
uses the effective relative nullity. A rank-nullity computation
on the actual even-selection domains proves, for all x,y,L,
pairLoss=finrank(completeRelationCode). The inclusion of that
actual code in the raw value kernel then proves pairLoss<=fullRank.
No regularity, positivity or independence premise is needed for
these exact algebraic comparisons. T1.8's dense estimate is now
specialized explicitly to the source's full arithmetic rank;
the earlier full raw-kernel theorem was the stronger input.
This closes a source-translation obligation, without an error
in the manuscript or an identification of the two ranks.

The weighted nonaligned residual in article Proposition 3.2
is now proved under exactly the same explicit generic normalized
curve and ordinary/chosen-source surface-cover properties.
The proved exponent is 1+epsilon, improving the printed
6/5+epsilon. This is recorded separately as P1-MATH-0113,
a confirmed implication CONDITIONAL on those exact geometric
properties; the external determinant and translation proofs
remain unformalized. It is not an unconditional exponent claim.

The proof removes the zero-pairLoss terms and partitions the
actual remaining host set by whether c>=epsilon*(L+1)/16.
The dense part has its already proved O(N^(1+epsilon/2))
source-kernel weighted bound. In the sparse part, the actual
raw kernel rank is at most the defective count plus c; the
unconditional defect estimate and binary-power conversion
bound each weight by N^(epsilon/4). The positive-pairLoss
support is literally a subset of PairHostCover.hosts, whose
stronger unconditional count is N^(1+epsilon/4). Multiplying
and summing proves the improved weighted bound, with all
constants and geometric caps fixed before the host data.
Local kernels, zero compatibility, irregular windows, contacts
and overlapping windows are all retained; no effective-rank
replacement or supplied support/count estimate is used.

NonalignedSourceResidualUnderInputs.uniform_source_bounds
packages both separated support and weighted residual counts
with exponent 1+epsilon. article_3_2 specializes these to both
literal printed 6/5+epsilon conclusions. Hence main 3.2 moves
to CONDITIONAL, not proved. T1.8 and main 3.4 remain conditional,
main 3.3 and T1.7 remain in_progress, and proved numbered
coverage stays 79/167. Confirmed improvements become 113,
including the explicitly conditional improvement just stated.
No manuscript conclusion error is confirmed. Original source
bytes, compiler and dependencies are unchanged; Palomar remains
deferred until completed coverage and actual input proofs.

Verified under Lean v4.36.0-rc2: full build passed (12741 jobs); direct axiom audit passed for 9234 declarations using only propext, Classical.choice and Quot.sound; all 7292 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.33 GiB.


## The actual all-ordered signed arithmetic pair profile

The signed arithmetic pair Fourier weight is now connected
literally to actual probabilities, nominal centering and the
second factorial cumulant. SourcePairAffineWeight constructs
eta as an actual zero/one compatibility indicator and proves
its equality to compatibility of the literal finite family
start system at every adequate cutoff. The exact identity is
q_xy=p^2*eta_xy*2^pairLoss, with p=(2^L)^(-1), including every
local kernel and incompatible pair. The scaled signed weight
is therefore q_xy-p^2. No regularity, positive probability or
effective-relative-rank replacement is assumed in this identity.

An exact finite sum over all ordered DISTINCT pairs proves
p^2*sum(eta*2^pairLoss-1)=kappa2+mu^2-(|G|p)^2+|G|p^2.
The actual diagonal is retained. The identity uses the literal
ordered/unordered multiplicity and actual falling factorial
moment. It applies to arbitrary dyadic subfamilies. The proved
mean bias, actual mean cap and nominal square bound then give
an UNCONDITIONAL error <=N^(-1+epsilon) between the scaled full
dyadic signed sum and the actual second factorial cumulant.
All centering and diagonal terms are recovered internally.

SignedSourceProfileUnderInputs.uniform_all_ordered combines
this identity with the conditional actual two-channel cumulant
profile. It proves, for ALL ordered distinct dyadic pairs,
|sum(eta*2^pairLoss-1)-N/3*(S_23(L)+S_34(L))|
<=N^(6/5+epsilon). The finite signed channel polynomials are
exact, including all lower-order terms. The two actual rational
translation coefficients are each exactly 1/3. The proof derives
the nominal unscaling estimate from the critical binary word
bound and composes all exponent and constant margins explicitly.
Only the previously identified generic normalized curve and
ordinary/chosen-source surface-cover properties remain inputs.
A fixed admissible prime threshold 8*(L+1) is selected internally;
the final source statement has no extra threshold parameter.

This is the ALL-distinct-pair variant, not yet the manuscript's
separated-pair display. Removing the close pairs still requires
its explicit contact comparison. The raw positive profile and
full phase-asymptotic alignment also remain open. Main 3.3 stays
in_progress and no complete raw pair-profile claim is made.
Main 3.2, main 3.4 and T1.8 remain conditional on the exact
geometric properties. Proved coverage stays 79/167, confirmed
improvements stay 113, and no new improvement identifier is
assigned to these source identities and proof compositions.
Original source bytes, compiler and dependencies are unchanged;
Palomar remains deferred and no manuscript-conclusion error
is newly confirmed.

Verified under Lean v4.36.0-rc2: full build passed (12749 jobs); direct axiom audit passed for 9247 declarations using only propext, Classical.choice and Quot.sound; all 7308 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.30 GiB.


## The literal separated signed arithmetic pair profile

The signed raw relation-count display of article Theorem 3.3
is now proved literally on separated ordered dyadic hosts under
the explicit geometric properties already identified. The new
article_3_3_signed theorem gives
|sum_(separated)(eta*2^pairLoss-1)-N/3*(S_23(L)+S_34(L))|
<=N^(6/5+epsilon). The source full arithmetic rank includes the
local kernels, eta is the actual affine compatibility indicator,
and both finite signed channel polynomials are retained whole.
There is no supplied separated host count or profile remainder.

The new contact comparison is unconditional. Exact finite
membership lemmas identify the ordered close hosts with distinct
pairs whose distance is at most L, and the complementary hosts
with precisely x+L<y or y+L<x. An exact partition identity
preserves both orientations and the actual multiplicity two.
The nominal squared mass of close pairs is bounded by
L*|G|*p^2 using a constant-weight disjoint-pair estimate.
The existing actual contact joint-mass bound handles every
positive close event, including compatible exact contacts.
No assertion that all close joint probabilities vanish is used.

The exact source Fourier identity converts p^2 times the absolute
signed source weight to |q_xy-p^2|. Sum the actual joint mass and
nominal close mass, retain the ordered multiplicity, and use the
proved critical-window word bound to remove p^2. This gives an
UNCONDITIONAL O(N^(1+epsilon)) total absolute signed weight on
all close hosts. It retains irregular windows, local kernels and
incompatible pairs. Subtracting this exact close population from
the previously proved all-ordered signed profile gives the
literal separated display. All finite partitions, powers,
constants and epsilon margins are internally proved.

Only the generic normalized curve property and the distinct
ordinary/chosen-source surface covers remain explicit unproved
arguments in the resulting signed-profile theorem. The contact
bridge itself uses no BCN or determinant argument. The positive
raw profile and the full source phase-asymptotic conclusions
remain open, so main 3.3 stays in_progress. Main 3.2, main 3.4
and T1.8 remain conditional. Proved numbered coverage stays
79/167 and confirmed improvements stay 113. These are source
translation and proof-composition advances, with no new
improvement identifier or manuscript-conclusion error.
Original source bytes, compiler and dependencies are unchanged,
and Palomar remains deferred.

Verified under Lean v4.36.0-rc2: full build passed (12755 jobs); direct axiom audit passed for 9257 declarations using only propext, Classical.choice and Quot.sound; all 7320 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.65 GiB.


## Positive arithmetic weights and actual unsigned private channels

The positive arithmetic profile now has an actual unsigned
unit enumeration and an unconditional private-channel theorem.
SourcePairPositiveWeight retains the literal source rank
pairLoss=2L-dim(S_x+S_y), including both local kernels, and
identifies its positive weight with the dimension of the actual
even unit relation space on private normalized pairs. There is
no affine-compatibility or positive-probability restriction.
A separate setWeight uses the full arithmetic rank on finite
families; its pair specialization is proved exactly.

The existing canonical selected-word equivalence is used to
count every nonzero even unit relation. Its literal finite
cardinality is 2^(number of units-1)-1. Reindexing by actual
source pairs and endpoint placements gives both orientations
of the unsigned host aggregate, with the actual coefficient
2*(2a-b)/(ab) and the finite U_ab(L), with endpoint error at
most 6*(L+1)*U_ab(L). No signed probability estimate is used
to infer this positive count, so incompatible principal pairs
are fully retained.

PrivateChannelPositiveMass.channelWeight is the sum of the
actual 2^pairLoss-1 over the actual private channelSources.
Its exact deletion identity subtracts precisely the nonprivate
unit aggregate. One-unit or zero-unit terms vanish by their
proved even-kernel dimension. The finite error is bounded by
6*(L+1)*U_ab(L) plus twice the actual nonprivate source count
times 2^((L+1)/b). Combining the proved square-root nonprivate
count, critical word bound and polynomial absorption yields
PrivateChannelPositiveProfile.uniform_error:
|channelWeight-N*coefficient(a,b)*U_ab(L)|
<=N^(1/2+1/b+epsilon), uniformly for fixed positive coprime
interior a<b<2a and 2b(L+1)<=H<=D(L+1). The coefficient is
therefore literally 1/3 in both principal channels. All these
results are unconditional.

A separate unconditional uniform source-power theorem on the
literal enlarged alignments gives 2^pairLoss<=N^(1/b0+epsilon)
for every height at least b0, up to (L+1)^3. The zero-exact-unit
version gives N^epsilon. The derivation uses the already proved
full source rank bounds and keeps local kernels. It introduces
no determinant or point-count assumption.

The remaining aligned residual populations, strict separated
source placement, disjoint principal-channel decomposition and
full phase-asymptotic conclusions are still to be assembled.
Thus these auxiliary theorems do not complete main 3.3; its
signed separated profile remains conditional on the explicit
geometric properties. Proved numbered coverage stays 79/167
and confirmed mathematical improvements stay 113. No new
external input, manuscript correction or improvement identifier
is introduced. Original source bytes, compiler and dependency
pins are unchanged; Palomar remains deferred.

Verified under Lean v4.36.0-rc2: full build passed (12767 jobs); direct axiom audit passed for 9284 declarations using only propext, Classical.choice and Quot.sound; all 7354 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.62 GiB.


## The literal positive separated source profile

The first display of article Theorem 3.3 is now proved literally:
|sum_(ordered separated)(2^pairLoss-1)-N/3*(U_23(L)+U_34(L))|
<=N^(6/5+epsilon). The source rank is exactly 2L-dim(S_x+S_y),
with local kernels retained. There is no compatibility filter.
PositiveSeparatedSourceProfileUnderInputs.article_3_3_positive
uses only the explicit normalized-curve and ordinary/chosen-source
surface-cover properties already recorded. For this positive
display the chosen-source component cap is sizeCap(epsilon/64),
with the embedding degree and all other caps selected before
those geometric arguments. The signed display has its separately
recorded fixed cap. No target mass or remainder is an input.

The entire aligned positive residual is unconditional. The proved
O(N^(1+delta)) support count for actual full-rank-loss pairs,
including irregular windows, combines with the proved enlarged
alignment power bounds to give O(N^(1+1/b0+epsilon)) mass on
all channels of height at least b0. Thus the height-five tail is
O(N^(6/5+epsilon)), without any additional point-count theorem.
Zero-unit alignments have O(N^(1+epsilon)) positive source mass.
The separated height-one boundary is contained in that actual
zero-unit population. The height-two boundary has O(N^(1/2+
epsilon)) mass, by its literal endpoint rectangle and full
source rank bound. Nonprivate fixed-channel sources have
O(N^(1/2+1/b+epsilon)) positive source mass, including incompatible
events; the actual unordered image is bounded as well.

StrictChannelSourceSeparation strengthens the existing weak
separation conclusion to x+L<y, under the same source-parameter
and size hypotheses. Its proof uses the actual exact-unit
translation and endpoint bounds; it does not discard contacts
by a probability assertion. Consequently both private principal
channels lie inside the actual separated-pair family. Their
unordered families are disjoint by the already proved slope
separation. The exact ordered multiplicity two and their actual
positive masses are proved, with both orientations retained.

A finite nonzero-weight cover classifies the aligned residual
outside the principal families into six actual populations:
separated height one, height two, the two nonprivate principal
channels, zero-unit alignments and the high tail. Private
one-unit terms vanish by their actual source kernel dimension.
Their unconditional bounds give the full aligned residual.
The conditional nonaligned mass bound applies to the actual
ordered host family, with no regularity or compatibility premise.
An exact positive decomposition then combines both complete
unsigned principal polynomials with the aligned and nonaligned
remainders. All constants and epsilon margins are internally
absorbed; a fixed threshold H=8*(L+1) is selected in the final
statement, which has no extra threshold parameter.

This completes the literal positive profile while preserving the
already proved literal signed profile. The final leading and
second-phase equivalents for the actual cumulant remain to be
assembled, so main 3.3 stays in_progress. Completed numbered
coverage stays 79/167 and confirmed improvements stay 113.
These are proof and statement-alignment advances; no new
correction identifier or external input is added. Compiler,
dependency pins and original manuscript bytes are unchanged.
Palomar remains deferred.

Verified under Lean v4.36.0-rc2: full build passed (12779 jobs); direct axiom audit passed for 9307 declarations using only propext, Classical.choice and Quot.sound; all 7382 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.59 GiB.


## Actual variance and both principal phases: conditional completion of theorem 3.3

All five conclusions of article Theorem 3.3 are now aligned
and proved under explicit geometric inputs, so its ledger status
is conditional rather than in_progress. This does not discharge
those geometric properties or increase unconditional numbered
coverage. The positive and signed ordered separated profiles
retain their exact finite U_23/U_34 and S_23/S_34 polynomials.
The existing P1-GEO-NORMALIZED-CURVE-UNIFORM,
P1-GEO-ORDINARY-SURFACE-COVER and
P1-GEO-CHOSEN-SOURCE-SURFACE-COVER properties remain unproved
ordinary theorem arguments, with the precise finite caps exposed
in the component declarations. The positive profile uses its
epsilon-dependent source component cap; the signed, cumulant
and phase declarations expose their fixed-density caps. No
common supplied target remainder or hidden axiom is introduced.

CountVariance proves that every actual finite infinite-model
start count is in L2, using its actual measurability and the
pointwise bound by the number of starts. Its Mathlib variance
is exactly E[Z^2]-(E[Z])^2. Hence the existing full second
factorial cumulant is literally Var(Z)-E[Z], with the diagonal
mean term retained. ActualPairPhaseUnderInputs.alpha uses that
actual variance and actual Bochner expectation, not a newly
postulated scalar. These identities are unconditional.

The principal height-three and height-four sums are identified
exactly with the actual 2:3 and 3:4 main terms. The nominal
parameter is literally lambda=N*2^(-L). The whole first-channel
term is exactly lambda^2/(3N)*S_23(L). The existing moving
height phases evaluate to the printed constants
(r3+2)/(18*2^(r3/3)) and (r4+3)/(24*2^(r4/4)), with powers
lambda^(5/3)*L*N^(-2/3) and lambda^(7/4)*L*N^(-3/4).
The identities hold for the actual residues L mod 3 and L mod 4.
No fixed-residue subsequence is substituted for the source claim.

Unconditional positive phase lower bounds show that every
strictly smaller power error is negligible uniformly in the
critical band. The entire finite 3:4 channel is negligible
relative to the 2:3 phase. The actual conditional cumulant
remainder is instantiated at the fixed exponent -31/40,
strictly below both phase exponents. Combining these facts
with the proved word-phase equivalents yields, for every
positive tolerance, a single threshold preceding every
critical L, and both relative errors at most that tolerance.
For the second phase, the entire finite S_23 is subtracted
before comparison; its lower-order internal terms are retained.
ActualPairPhaseUnderInputs.article_3_3_phases gives the two
literal source ratios and article_3_3_cumulant gives the
literal actual-variance-minus-mean expansion with error
N^(-4/5+epsilon). Positivity of both phase denominators is
proved inside uniform_phases.

The new COMPLETE_PAIR_PROFILE_ALIGNMENT note maps all five
displays and the actual probabilistic quantities to their Lean
declarations and records the residual external scope. Main 3.2,
3.3, 3.4 and companion T1.8 are conditional on the previously
identified geometric properties. Unconditionally proved
numbered coverage stays 79/167 and confirmed mathematical
improvements stay 113. No new correction identifier is needed:
these are the remaining exact translations and proof assemblies
of the source theorem. Original manuscript bytes, compiler and
dependency pins are unchanged. Palomar remains deferred until
the full development, external inputs and alignment are complete.

Verified under Lean v4.36.0-rc2: full build passed (12785 jobs); direct axiom audit passed for 9324 declarations using only propext, Classical.choice and Quot.sound; all 7400 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.57 GiB.


## Homogeneous dependent pairs outside the raw principal family

The outside-principal residual in the first numbered clause of
companion T1.12 is now proved under the already identified
geometric properties. HomogeneousPairResidualUnderInputs.
companion_T1_12_pair_residual gives the literal W-mass bound
N^(-4/5+epsilon) on all dependent, strictly separated pairs of
any regular dyadic subfamily, outside the actual raw principal
family. The affine-compatibility condition is absent. The exact
same bound is proved for the sum of the actual homogeneous
zero-target probabilities over that actual population. The
private cutoff satisfies 8(L+1)<=H<=D(L+1), with D fixed and
all subfamilies varying after the common threshold.

The new unconditional probability bridge uses the full source
pairLoss, including local kernels. The actual homogeneous pair
probability is exactly p^2*2^pairLoss even on irregular windows.
The full pair-span dimension plus pairLoss is proved equal to
2L. On regular distinct pairs, pairLoss equals the actual
effective relative nullity, by the exact two-space dimension
identity and the actual local ranks. The source W weight can
therefore be used on the regular set without silently asserting
a nominal relative-nullity formula on irregular windows.
For positive source loss, the elementary bound
2^rho<=2*(2^rho-1) is proved, with its full scaling.

The finite off-principal positive mass is bounded by the actual
positive profile error and the two actual private-channel errors,
using the exact ordered multiplicity and disjoint private
principal families. Combining the proved literal positive
profile with the unconditional private-channel errors gives
RawPairResidualUnderInputs.uniform_bound:
sum_(separated outside raw principal)(2^sourceLoss-1)
<=N^(6/5+epsilon), uniformly over the admissible private cutoffs.
No supplied off-principal count or mass is an input. The public
geometric component cap is sizeCap(epsilon/128), and all other
finite caps precede the explicit geometric arguments.

The actual regular dependent-pair population is defined and
proved to lie in that original separated off-principal family.
Its W weight is at most twice p^2 times the positive source
weight. The proved critical nominal-square upper bound and
constant absorption yield the printed N^(-4/5+epsilon) rate.
The final public component cap is sizeCap(epsilon/384), with
the exact normalized curve and ordinary/chosen-source cover
properties as explicit unproved arguments. This is a geometric
conditional proof, not an unconditional certification or a
postulate of the target residual bound.

Together with the previously proved unconditional raw principal
seed upper/lower scale, this closes clause (1) of T1.12 under
those geometric properties. Clauses (2) and (3), involving
dependent targets and two distinct good edges, remain open;
T1.12 stays in_progress. The asymmetric large-prime profile
T1.10 is not asserted proved by these pair results. Main 3.3
remains conditional with all five conclusions aligned. Coverage
stays 79/167 and confirmed improvements stay 113. These are
proof-composition advances without a new correction identifier.
Original manuscript bytes, dependencies, compiler and Palomar
state are unchanged.

Verified under Lean v4.36.0-rc2: full build passed (12791 jobs); direct axiom audit passed for 9337 declarations using only propext, Classical.choice and Quot.sound; all 7414 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.55 GiB.


## Actual ternary prime groups and center-independent forced planes

The finite arithmetic and plane-forcing core of companion T1.16
is now proved for actual prime groups on three arbitrary finite
sets of positive integers. This is the source ternary group
budget, not the separate abstract ternary selection theorem T2.3.
The final CRT tail sums and fixed-k induction are still open,
so T1.16 moves from not_started to in_progress, not proved.

TernaryPrimeGroups constructs the actual finite value-triple
pool and, for each triple, the product of exactly the primes
above H with odd valuation in all three entries. Membership,
primality, positivity, squarefreeness and divisibility of every
entry are proved. A prime above the common diameter cannot
occur at two different values in a block. Consequently the
prime sets of distinct actual triples are disjoint, their
products are coprime, and all active group values greater than
one are distinct. The strict decreasing-order convention in
the source therefore causes no hidden tie issue. The literal
support-pool cardinality is the product of the three set sizes.

The arithmetic rigidity is proved for arbitrary finite sets.
Injectivity of an even-selection map implies injectivity of
its data vectors, by the two-coordinate zero-sum selection.
For the finite forcing argument it suffices that the parity
vectors of distinct local values are distinct, together with
pairwise disjoint even square-class images. Proportional
positive value pairs would give the same nonzero even class
in two disjoint images, which is impossible. The three-block
projection rigidity is derived from these actual arithmetic
hypotheses; it is not an assumed geometric exclusion.

Actual products of two groups divide every corresponding
2x2 integer minor. If values are at most A and within-block
diameters are at most H, the minor is at most 2AH. A shared
value is handled separately using coprimality and product
divisibility. This gives the uniform finite bound 2A(H+1).
The product of three actual groups divides their 3x3 determinant,
whose absolute value is at most 6AH^2. A group product greater
than this threshold forces the determinant to vanish.

The collinear exception is excluded without a primitive-direction
choice. Put d=v-u for the first two value triples. If u,v,w
are collinear, d cross u=d cross v=d cross w. Every actual
group therefore divides all coordinates of the same integer
cross vector. Pairwise coprimality makes their product divide
it, while each coordinate is at most 2AH. A larger product
forces the cross vector to vanish. The actual pairwise
square-class rigidity then forces u=v, contradicting distinct
supports. Thus, for H>=1, product>6AH^2 forces a genuine plane.
Every normal coordinate is proved nonzero, using the actual
positive projection rigidity and the vanishing determinant.
This unconditional finite simplification and weaker local
hypothesis are recorded as P1-MATH-0114. It is not an assertion
of the still open asymptotic counting bound.

For centers X and offsets bounded in absolute value by R,
the normal is identified with the cross product of offset
differences; it is independent of a common center translation.
Each normal coordinate has absolute value at most 8R^2 and
the plane constant is at most 24R^3. The centers satisfy the
actual resulting integer-plane equation. The actual plane
belongs to an explicitly defined pool depending only on R,
of cardinality (16R^2+1)^3*(48R^3+1). The plane is genuine and
all its normal coordinates are nonzero. No target plane,
primitive vector, rank premise or host count is postulated.

All these finite results are unconditional. The remaining
T1.16 obligation is the uniform tuple count
N^epsilon*(N^3/T^2+N^(6/5)), including actual CRT encoding,
hyperbolic reciprocal sums and the fixed-k induction. No new
external input is added. Coverage stays 79/167; main 3.3 stays
conditional and T1.12 clauses (2),(3) remain open. Confirmed
mathematical improvements total 114, with the exact finite
scope of the new finding retained. Original source bytes,
compiler and dependency pins are unchanged; no new Paper C
source is copied and Palomar remains deferred.

Verified under Lean v4.36.0-rc2: full build passed (12803 jobs); direct axiom audit passed for 9377 declarations using only propext, Classical.choice and Quot.sound; all 7463 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.52 GiB.


## Actual ternary groups: both CRT counting regimes

The two CRT counting regimes in the proof of companion T1.16
are now proved on actual finite center populations, with the
three sets of values, their prime cutoff and their height cap
allowed to vary after the uniform threshold and with the center.
The sets themselves are never enumerated. The finite covers
enumerate only actual group products, their ordered positive
factorizations and bounded integer offsets.

IntegerOffsetCRT cancels arbitrary signed integer offsets in
two divisibility conditions and proves equality of the residue
classes. Pairwise coprimality combines all moduli. Each actual
coordinate in an interval of length N has at most N/Q+1 values;
an actual d-dimensional population has at most (N/Q+1)^d points.
No CRT solution is chosen, and no lower endpoint or offset
positivity is required. PlaneOffsetCRT proves that two actual
coordinates determine the third on an integer plane with
nonzero third normal coordinate. The corresponding count is
(N/Q+1)^2. The forced planes previously constructed have every
normal coordinate nonzero, so this condition is discharged.

ProductFactorizations constructs the actual finite pool of
ordered k-factor decompositions of Q, with cardinality at most
tau(Q)^k. The already proved elementary divisor estimate yields
a uniform subpower bound at every fixed polynomial product
height. CRTProductCover constructs the actual center cover,
including its coprimality and divisibility filters. Its offset
pool has exactly (2R+1)^(dk) members.

FiniteCRTTails transfers finite positive integer and positive
pair sums into the already proved summable p-series and
hyperbolic tails. The elementary inequalities
(a+1)^3<=4(a^3+1), a>=0, and (a+1)^2<=2(a^2+1)
remove all intermediate reciprocal terms. The finite cubic
sum is at most 8N^3*T^(-2)+4V for T<q<=V. The finite square
sum over positive pairs with ab>T is at most
2*C_2*N^2*T^(-1)*log(2T)+2*#pairs. Thus the source's separate
reciprocal-product logarithmic-square sum is unnecessary.
This checked proof simplification is P1-MATH-0115.

CRTProductRange proves the weak-regime count, retaining the
literal offset factor and uniformly paying for actual ordered
factorizations by M^epsilon. PlaneProductCover proves the
strong-regime count over any actual finite plane pool and only
two positive group sizes. The positive-product divisor count
pays for the latter size pool by V*M^epsilon. The third group
is not enumerated a second time.

TernaryTopProducts defines the actual maximum over products of
k distinct active groups, with value zero when too few exist.
The maximum is proved attained whenever positive, and every
selected product is bounded by it. Injective finite enumerations
give its actual group vectors. TernaryGroupCertificates proves
that these groups supply the actual offset-CRT certificates.
For a triple with product above 6AH^2 and whose squared product
exceeds T^3, an actual pair has product>T and <=2A(H+1), and the
center belongs to the actual two-group cover of the previously
constructed finite plane pool. No count or plane is postulated.

TernaryGroupCounts proves both uniform regimes for arbitrary
finite center populations with center-dependent arithmetic
sets. The weak bound is
M^epsilon*(2R+1)^(3k)*(8N^3/T^2+4V).
The strong bound is the exact plane-pool cardinality times
(2R+1)^6 times
(2*C_2*N^2*log(2T)/T+2V*M^epsilon).
All local data injectivity, disjointness, positive value and
diameter hypotheses in the strong bound are the actual
arithmetic predicates. The top-product height bound <=A^k is
also proved from actual group divisibility. These statements
have no new external input and no assumed target count.

The final critical-band absorption, the choice V=N^(6/5), and
the fixed-k induction remain open. Accordingly T1.16 stays
in_progress, numbered coverage stays 79/167, and main 3.3 stays
conditional. Confirmed improvements total 115. The compiler,
dependency pins and original manuscript bytes are unchanged;
no new Paper C source is copied and Palomar remains deferred.

Verified under Lean v4.36.0-rc2: full build passed (12823 jobs); direct axiom audit passed for 9421 declarations using only propext, Classical.choice and Quot.sound; all 7518 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.49 GiB.


## Companion T1.16: the full actual ternary group budget

Companion Proposition T1.16 is now proved unconditionally,
including its actual tuple count, the final critical-band
absorption, the fixed-k induction, offset-pattern multiplicity,
and the source prime cutoff without an upper bound.
The public theorem is TernaryUnboundedCutoff.companion_T1_16;
actual_tuples_bound applies it to the literally defined finite
tuple population, not an abstract supplied count. The final
bound is N^epsilon*(N^3/T^2+N^(6/5)), for every fixed k>=3,
and in fact for every real T>=1, covering the printed range
1<=T<=N. The original common convention B=L+1 and critical
band is recorded in companion_sections/guide.tex:19-38.

One threshold, depending only on C,D,k,J,epsilon, precedes all
lengths and radii, the arbitrary type of offset-pattern labels,
their actual finite pool of size at most B^J, all actual center
populations, all assignments of the three arithmetic sets,
their cutoff choices, base intervals and the real threshold T.
The parameter J permits polynomially many actual pattern labels;
this includes the source's fixed number of offset patterns.
No regular-set, probability or affine-compatibility premise is
used. Values are actual positive integers of height at most DN,
within R<=DB of the centers. Center boxes have side length DN;
no lower center bound is required. A fixed natural D can enlarge
any fixed source height and width comparison constants.

TernaryGroupScales proves the exact polynomial bounds for the
offset and plane pools and their uniform critical-band absorption.
It proves 6(DN)H^2<N^(6/5) and 2(DN)(H+1)<=N^2 uniformly when
H<=DB, and bounds log(2N^(4/5)) by a fixed multiple of B.
The plane-pool and two-group-offset factor is bounded by
17^3*49*(2R+1)^15. All constants and fixed polynomial degrees
are paid for by positive power margins; no asymptotic factor
is inserted as an assumption.

TernaryWeakCritical proves the full weak count for any fixed k
and all T>=1, with product cutoff V arbitrary and nonnegative.
The actual group height <=DN proves topProduct<=N^(2k)
eventually, discharging the ordered-factorization height cap.
TernaryStrongCritical proves the actual three-group tail above
N^(6/5) is at most N^(6/5+epsilon). Its two-group threshold is
N^(4/5). The first term is N^2*N^(-4/5)*log(2N^(4/5)); the
second counts actual pairs of sizes with product O(NB), using
the already proved divisor estimate with a fixed margin 1/10.
The actual forced plane and finite offset pool are retained
throughout. Combining the weak and strong populations proves
the full three-group budget.

TernaryTopProductDrop deletes a smallest element of an actual
maximizing k-selection and proves
G_k^(k-1)<=G_(k-1)^k. Thus G_k>N^(6/5) forces
G_(k-1)>N^(6(k-1)/(5k)). For every k>=4 this exponent is at
least 9/10. The same preceding-order cutoff N^(9/10) therefore
works at every induction step, and N^3/N^(18/10)=N^(6/5).
This removes the source's separate k=4, k=5 and k>=6 cases.
The strong induction is fully proved in TernaryGroupBudget;
it does not accept a previous-order target bound as an external
argument. This simplification is recorded as P1-MATH-0116.

TernaryLargestSelection identifies an actual maximizing
k-selection with the k strictly largest active groups: every
outside group is strictly smaller than every selected group.
The previously proved active-value injectivity removes ties.
The canonical maximum product is zero when fewer than k active
groups exist. This aligns the finite maximum with the source's
decreasing-order convention without assuming a sorted list.

TernaryPatternBudget counts actual labeled tuples and absorbs
their B^J pattern multiplicity, with the threshold before the
label type. The source full even-map injectivity is explicitly
converted to the weaker local parity injectivity used by the
internal budget. Pairwise disjoint actual even images are
retained. No local kernel or directness condition is hidden.

The source only requires H to exceed the three diameters;
there is no upper bound on H in the final public statement.
TernaryCutoffMonotonicity proves actual prime-pool inclusion,
group divisibility and size monotonicity, active-support
inclusion and top-product monotonicity. Replace H internally
by min(H,2R+1): this still dominates the actual diameters and
has a fixed logarithmic ceiling, while every counted top
product can only increase. TernaryUnboundedCutoff proves this
reduction and the final actual finite-tuple theorem. The
source cutoff may vary both with the pattern and the center.

T1.16 moves from in_progress to proved. Numbered coverage is
now 80/167; confirmed mathematical improvements total 116.
Main 3.3 and the other identified geometric applications stay
conditional, and T1.12 clauses (2),(3) remain open. This result
adds no unproved external input, copies no further Paper C
source, and changes no original manuscript byte or dependency
pin. Palomar remains deferred until the full two-document
formalization and statement alignment are complete.

Verified under Lean v4.36.0-rc2: full build passed (12845 jobs); direct axiom audit passed for 9452 declarations using only propext, Classical.choice and Quot.sound; all 7557 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.44 GiB.


## T21.4: actual polylogarithmic group confinement in three dimensions

The full three-dimensional support-group branch of companion
T21.4 is now proved on actual finite tuple populations. The
individual-prime branch and the fixed-affine-plane variant
remain open, so the numbered proposition moves from not_started
to in_progress, not proved. Coverage stays 80/167 and confirmed
improvements stay 116; this is a proof-composition advance.

ProductConfinement proves the deterministic finite argument.
If all selected k-products of a finite factor set are <=N,
at most k-1 factors exceed N^(1/k). If the remaining product
exceeds N, a minimum-cardinality crossing subset has product
in (N,N^(1+1/k)] and all its factors are <=N^(1/k). Otherwise
the count of factors>Y is at most floor(log N/log Y), proved
by the actual finite logarithm-of-product identity. These
claims require neither primality nor an assumed stopping rule.

TernaryValueConfinement applies this to the actual group-value
pool. Group values and support labels have the same cardinality
by actual active-value injectivity. Their pairwise coprimality
is proved, every selected product is bounded by the actual top
product, and the crossing subset is shown to provide genuine
integer-offset CRT certificates for its actual centers.

CRTSupportCover canonically enumerates a finite set A of factor
sizes, rather than paying for all their orderings. The offset
cost is exactly (2R+1)^(3*card A). A certificate product Q>N
in a box of side DN has at most (D+1)^3 centers for each offset
assignment. The actual finite cover over all such A is bounded
by (D+1)^3 times the literal integer-factor weighted count of
T21.3. Coprimality is retained while applying CRT and only then
dropped in the positive Rankin sum. No target count is assumed.

RankinCertificateCritical combines that actual cover with the
already proved T21.3 integer-factor bound and the verified
sublinear-logarithmic exponential estimate. For any fixed
0<zeta<1 and k>=1 its count is at most
N^((1+1/k)*(1+(2+zeta)/c)+epsilon), uniformly over critical
lengths and bounded radii, all center base intervals and all
actual integer factor subsets. PolylogConfinementScales chooses
zeta and k before N so the extra exponent is arbitrarily small.
It also proves, uniformly in the critical band, that
k-1+floor(log N/(c log B))=o(L), with a literal statement for
every positive comparison constant and B=L+1.

TernaryGroupConfinement proves the actual exceptional-center
count N^(max(6/5,1+2/c)+epsilon). The first population has actual
topProduct>N and is counted by the completed T1.16. Every point
in the second population supplies an actual crossing certificate
and belongs to the Rankin cover. The two populations cover the
entire excessive-group family. The integer k depends only on
c,epsilon and precedes C,D, the actual sets and cutoff choices.
The source cutoff has no upper bound here.

LabeledPopulationCount proves a general finite label-fiber count.
TernaryConfinementMass uses it to include B^J actual offset-pattern
labels, with one threshold before the label type, all arithmetic
assignments and nonnegative weights. For point weights at most
N^(-beta+epsilon/2), the actual excessive-group population has
mass at most
N^(-min(beta-6/5,beta-1-2/c)+epsilon).
The remaining error margin pays for the count and labels. This
is the source's uniform N^(-beta+o(1)) weight regime made explicit;
it is not an assumed exceptional-count or exceptional-mass bound.
The actual exceptional finite set is defined, its mass is bounded,
and every retained tuple has at most
k-1+floor(log N/(c log B)) actual groups greater than B^c.

TernaryGroupNegligibility proves that c>6 makes
max(6/5,1+2/c)<4/3. It supplies a fixed positive point-weight
margin theta and a fixed k such that for every eta>0, eventually
the actual exceptional mass is <=eta*L*N^(-2/3), whenever each
host weight is in the beta=2 class, at most N^(-2+theta).
The retained count is the same literal source expression. This
is the sufficient c>6 assertion for the three-dimensional group
branch. No c>3 fixed-plane claim is made at this checkpoint.

The remaining T21.4 work is explicit: the individual-prime
fixed-k budget must account for repeated offset supports, and
the specified-plane CRT cover must enumerate only two free
offset coordinates to obtain the 1/c exponent and c>3 threshold.
No new literature input, Paper C copy, original source change,
dependency update or Palomar registration is introduced.

Verified under Lean v4.36.0-rc2: full build passed (12863 jobs); direct axiom audit passed for 9482 declarations using only propext, Classical.choice and Quot.sound; all 7597 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.40 GiB.


## T21.4: the complete individual-prime branch in three dimensions

The individual-prime branch of companion T21.4 is now proved
in three dimensions, in addition to the previously completed
support-group branch. The remaining obligation is the specified
finite-family-of-affine-planes variant with its 1/c exponent
and sufficient c>3 threshold. T21.4 therefore stays in_progress;
numbered coverage stays 80/167. The two checked simplifications
below are P1-MATH-0117 and P1-MATH-0118, bringing the confirmed
improvement total to 118 without asserting a manuscript error.

TernaryIndividualPrimes constructs the actual finite pool of
primes above H with odd valuation in an actual value in every
block. Its membership is the literal existence of a support
triple in the actual pool. Each such prime is proved prime and
its support group active. A selected finite product of distinct
primes divides the product of its actual covering support groups.
If at most two support groups occur, the previously proved
one- and two-group bounds give a product <=2A(H+1). Thus three
selected primes above this threshold must occupy three supports,
and their product is at most the actual three-group top product.
This handles every repeated-support case without a new cross
product or collinearity proof. The large-prime tail reuses the
already proved actual three-group forced-plane count. This is
the unconditional proof simplification P1-MATH-0117.

FiniteFactorTopProducts proves the canonical largest k-product
for an arbitrary actual finite set of integer factors. It is
attained when positive, is zero when too few factors exist,
and a maximizing selection consists of the strictly largest
factors when they are positive. The smallest-factor deletion
inequality and its arbitrary real-exponent threshold consequence
are proved. No decreasing-order convention or induction target
is supplied as an input.

TernaryPrimeTopProducts constructs the actual individual-prime
top product, proves its height <=A^k and its monotonicity as the
prime cutoff increases, and constructs the actual offset-CRT
certificate of every positive maximizing selection. The prime
sizes are pairwise coprime because they are distinct actual
primes. Their offset supports may repeat. TernaryPrimeCounts
and TernaryPrimeWeakCritical prove the weak product count from
this literal certificate and the actual ordered-factorization
pool, with uniform critical-band absorption.

TernaryPrimeBudget proves the complete individual-prime fixed-k
budget N^epsilon*(N^3/T^2+N^(6/5)) for every fixed k>=3. Its
three-prime strong sector is bounded by the actual group sector
using the support-merging argument. The same N^(9/10) preceding
cutoff works throughout the strong induction. TernaryPrimeTheorem
retains arbitrary source cutoffs with no upper bound by the
already checked internal cap min(H,2R+1), and includes B^J
actual pattern labels with one threshold before the label type.
The source full even-map hypotheses are retained explicitly.

TernaryPrimeValueConfinement supplies the deterministic
confinement-or-certificate alternative for actual primes>B^c.
The crossing certificate belongs to the same integer-factor CRT
cover used for support groups. In particular, the separate
prime-only Euler product is unnecessary for the final T21.4
bound: use the proved integer-factor Rankin bound with any fixed
positive zeta, choose zeta small and k large before N, and absorb
the extra exponent in epsilon. The exponential in B^(1-zeta)
is uniformly subpolynomial. This is P1-MATH-0118; it simplifies
this application without replacing the sharper prime estimate
already proved in T21.3 or changing its statement.

TernaryPrimeConfinement proves the actual excessive-prime count
N^(max(6/5,1+2/c)+epsilon). TernaryPrimeConfinementMass counts
all actual pattern labels and proves the literal exceptional
mass N^(-min(beta-6/5,beta-1-2/c)+epsilon), for nonnegative
host weights in the source's uniform N^(-beta+o(1)) class.
The exact point-weight margin epsilon/2 is exposed. The actual
exceptional finite set is defined, its mass is bounded and every
retained tuple has at most k-1+floor(log N/(c log B)) individual
primes above B^c. The uniform o(L) conclusion follows from the
previously checked logarithmic-count scale theorem.

TernaryPrimeNegligibility proves the sufficient c>6 assertion
for beta=2, with a fixed positive point-weight margin and a
fixed k chosen before N. For every eta>0 the actual exceptional
mass is eventually <=eta*L*N^(-2/3). The argument is unconditional
within the explicitly stated positive-host-weight regime; it
assumes neither the exceptional population count nor its mass.

Only the fixed-plane 1/c and c>3 branch of T21.4 remains open.
No unproved geometric or analytic input is introduced by these
prime results, no further Paper C source is copied, and the
original manuscript and dependency pins remain unchanged.
Palomar remains deferred until the full work is complete.

Verified under Lean v4.36.0-rc2: full build passed (12885 jobs); direct axiom audit passed for 9515 declarations using only propext, Classical.choice and Quot.sound; all 7635 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.36 GiB.


## Complete companion T21.4: polylogarithmic confinement

Companion Proposition T21.4 is now complete, including both
actual support groups and actual individual primes, all ordinary
three-dimensional and specified-affine-plane mass estimates,
the literal retained-count bound and its uniform o(L) consequence,
and the sufficient c>6 and c>3 thresholds. It moves from
in_progress to proved. Numbered coverage is now 81/167; confirmed
mathematical improvements stay 118. This checkpoint closes the
remaining source obligations without a new correction identifier.

FreePlaneCRT proves that only two congruence coordinates are
needed on any genuine real affine plane. Choose a coordinate
with nonzero normal entry and project onto its two complementary
coordinates. The finite sum identity isolates the omitted
coordinate, proving injectivity of this projection. The actual
integer-offset residue population therefore has at most
(width/Q+1)^2 points. Plane coefficients are arbitrary real
numbers: there is no rationality, height or quantitative lower
bound on the nonzero normal coefficient. One common threshold
precedes the actual choice of planes and coefficients.

PlaneSupportCover defines actual finite plane-restricted CRT
populations. The canonical enumeration of a factor set A costs
exactly (2R+1)^(2*card A) offset codes. The third offset is never
an enumeration label. All three possible omitted coordinates
are covered by a factor 3. For Q>N and width DN, summing over
the actual finite plane pool gives the finite bound
3*#planes*(D+1)^2*integerWeightedCount(Y,V,(2R+1)^2).
Actual three-coordinate certificates restricted to a genuine
plane are proved to belong to this new two-coordinate cover.
This transfers both previously constructed group and prime
crossing certificates without assuming a plane-count estimate.

PlaneRankinCritical applies the already proved integer-factor
Rankin bound with d=2. With at most B^K actual planes, its
critical-band certificate count is at most
N^((1+1/k)*(1+(1+zeta)/c)+epsilon).
The arbitrary plane family, all coefficients, center intervals,
lengths, offsets and factor sets vary after the common threshold.
The polynomial plane multiplicity and the sublinear-logarithmic
exponential are absorbed using proved estimates. There is no
new external geometric or analytic argument.

PlaneTernaryConfinement proves a single simultaneous exceptional
count for excessive support-group OR individual-prime populations.
The two actual top-product>N populations are bounded by the
completed fixed-k budgets. In the remaining population, either
excess supplies an actual crossing certificate; its genuine
plane places the point in the two-coordinate Rankin cover.
The resulting count is N^(max(6/5,1+1/c)+epsilon).
The same parameter choice k,zeta already used in three dimensions
suffices, because the d=2 excess exponent is smaller.

PlaneConfinementMass includes B^J actual offset-pattern labels
and up to B^K real planes for each label. A common threshold
precedes the label type, all actual assignments and all weights.
Its actual_plane_confinement theorem defines the actual common
exceptional finite set and proves its positive mass at most
N^(-min(beta-6/5,beta-1-1/c)+epsilon).
Outside it, BOTH the actual support-group and individual-prime
counts above B^c are bounded by the same
k-1+floor(log N/(c log B)). The source point-weight regime is
made explicit as 0<=w<=N^(-beta+epsilon/2). Uniform o(1) point
errors fit this regime eventually; neither an exceptional count
nor an exceptional mass is an input.

PolylogConfinementTheorem.companion_T21_4_three_dimensional
likewise provides ONE actual exceptional set and a common k for
both ordinary three-dimensional populations. It combines the
previously proved group and prime branches using the maximum
of their fixed k values, the monotonicity of the literal count
threshold and positivity of the actual finite union mass. Its
mass exponent is exactly the printed
-min(beta-6/5,beta-1-2/c)+epsilon.
The final point-weight margin epsilon/4 is explicit. The earlier
PolylogConfinementScales.logarithmic_count_sublinear gives the
uniform o(L) conclusion for every such fixed k.

The simultaneous three-dimensional sufficient-cutoff theorem
proves the beta=2 exceptional mass is o(L*N^(-2/3)) whenever
c>6. PlaneConfinementNegligibility.sufficient_cutoff proves the
same conclusion on the specified plane populations for c>3.
Both give a fixed positive point-weight margin and a fixed k,
then for every eta>0 a common threshold such that the actual
exceptional mass is <=eta*L*N^(-2/3). These are sufficient
thresholds, exactly as in the source, with no optimality claim.

PrimitiveTripleWeights also discharges the source beta=2 weight
regime for actual original primitive full-rank triples. For an
injective primitive triple, its first pair is a proper subfamily
and has zero relative nullity, hence disjoint actual square-class
spaces. The full local ranks identify its homogeneous pair
probability with p^2. Monotonicity bounds the full homogeneous
triple probability by p^2; the actual affine triple probability
is bounded by the already proved direct-pair formula. The
uniform critical nominal-square estimate and constant absorption
give both actual probabilities in the class
0<=w<=N^(-2+theta), for every fixed theta>0. Full local ranks,
primitive status and injective original starts are actual
predicates, not supplied probability bounds. This bridge keeps
affine incompatibility and zero actual probabilities intact.

All T21.4 branches are unconditional under the source arithmetic
and positive-host-weight hypotheses. No new literature input,
Paper C source, original manuscript edit, dependency change or
Palomar registration is introduced. Main 3.3 and its identified
geometric applications remain conditional, and the open dense
edge and target bounds are unchanged.

Verified under Lean v4.36.0-rc2: full build passed (12903 jobs); direct axiom audit passed for 9546 declarations using only propext, Classical.choice and Quot.sound; all 7674 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.32 GiB.


## Sharp heterogeneous conversion and complete finite pair partition, under explicit geometric inputs

The literal source-scale heterogeneous conversion in article 15.1
and the complete finite-channel pair partition in companion T7.1
are now proved CONDITIONALLY on the already inventoried normalized
curve and ordinary/chosen-source surface-cover properties. Both
ledger rows move from in_progress to conditional. No geometric
property is discharged here. Unconditionally proved numbered
coverage stays81/167; confirmed mathematical improvements stay118.
This checkpoint assembles actual source statements and consequences
of P1-MATH-0113 without claiming a new unconditional exponent.

SharpPairActivityUnderInputs first combines the actual full second
factorial cumulant profile with the unconditional nonnegative gap
between absolute pair activity and half that cumulant. The full
original dyadic activity therefore equals the actual principal
beta up to N^(-4/5+epsilon). Every covariance sign, affine
incompatibility, zero marginal and locally irregular window is
retained. The already proved aligned activity and principal gap
then give A2(G)<=N^(-2/3+epsilon) for every deterministic subset G
of the original dyadic block, with one threshold before G and L.
The geometric source component cap remains the fixed1/100 used
by the existing cumulant profile. No target A2 bound is assumed.

SharpRunConversionUnderInputs applies the already unconditional
finite heterogeneous signed-measure theorem. The exact independent
Bernoulli product and every actual covariance are retained in B2;
mu is the actual first moment, and alpha is the complete actual
second factorial cumulant including its marginal-square diagonal.
The mean and marginal caps and the new A2 estimate discharge every
term of the finite error bound. The actual infinite sum of absolute
singleton differences between B2 and Q(mu,alpha) is at most
N^(-5/3+epsilon), as printed in article15.1. The same development
gives |alpha(G)|<=N^(-2/3+epsilon) uniformly for all deterministic G.
No complete-count-law approximation is inferred from this finite
reference conversion. The earlier generic theorem supplies the
first displayed finite inequality in15.1 without a small-marginal
premise; only its arithmetic rate is conditional.

SourcePairActivityBound proves a separate unconditional finite
majorant for the actual nonaligned activity. Nonzero covariances
are represented by increasing actual full-loss hosts. Positive
full source loss gives2^loss<=2*(2^loss-1), so the actual joint
mass is bounded by twice the nominal-square-scaled full source
weight. Negative covariance is retained through the actual host
independent mass. The complete conditional nonaligned source
weight bound from P1-MATH-0113 and the unconditional host independent
mass imply that the ENTIRE original nonaligned activity is at most
N^(-1+epsilon), including contacts and locally irregular windows.
Its exposed source cap isepsilon/32, not the fixed-density cap of
the separate sharp conversion. These interfaces are kept distinct.

FiniteAlignedChannelCover constructs the actual fixed finite set
of reduced interior slopes3<=b<=Q. It proves the enlarged aligned
classification at arbitrary Q, including the exact1:1 and1:2
boundary channels, the fixed-height private and normalized-defect
populations, zero-unit alignments and the high-height tail. No
constant-channel enumeration or source rank estimate is an input.

FiniteGoodChannelPartition defines three actual disjoint classes
of dependent pairs: positive private pairs in those fixed channels,
the remaining high-height pairs, and the complementary exceptional
pairs. Their union is the actual dependent family. Its exact
absolute-activity decomposition is proved, not supplied as a
partition hypothesis. Every good pair has an actual source channel
and the full GoodEdgeCompression.Conclusion: injective even-selection
map, equality of the compressed space with the original pair sum,
its exact rank, the source lower rank and a finite logarithmic-width
translation motif. The conclusions hold at every fixed retained
height, not merely in the two principal channels.

FiniteChannelActivityBounds proves simultaneous finite-family
bounds for all actual private and defective channel populations.
The selected cutoff is H=2Q(L+1), which satisfies the individual
channel width requirements for every b<=Q. The defective union
costs N^(-1+epsilon), the private union costs N^(-2/3+epsilon),
and every private coefficient has the literal pointwise bound
N^(-2+1/b+epsilon). The common threshold precedes all actual
populations and all critical lengths.

FiniteGoodPartitionUnderInputs.companion_T7_1 chooses Q after
eta>0 and BEFORE C, epsilon, all geometric input data and N.
It proves the actual weak activity<=N^(-1+eta+epsilon), actual
exceptional activity<=N^(-1+epsilon), sharp total pair activity,
and the individual good-pair weight and exact compression. The
exceptional activity is bounded by the actual nonaligned, two
boundary, zero-unit, fixed-defect and incompatible populations.
The source cap is preciselyepsilon/128 in the final declaration,
with finite auxiliary caps and quantifier order exposed. It is
not a supplied pair-activity or pair/target-deficit assumption.
The three classes remain disjoint by their actual set definitions;
no uniqueness of an auxiliary representation is presumed.

The finite classification, partition, compression and finite
reference-conversion inequalities are unconditional. Only the
identified geometric counting arguments are external. No new
literature input, global axiom, Paper C source, dependency download,
original manuscript edit or Palomar registration is introduced.
The sharp pair/target deficit of11.1, incompatible-triple3/2 rate,
conditional Palm estimates and dense primitive triple estimates
remain open. The next step is to count actual dependent targets
after a compressed fixed-channel source.

Verified under Lean v4.36.0-rc2: full build passed (12919 jobs); direct axiom audit passed for 9567 declarations using only propext, Classical.choice and Quot.sound; all 7703 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.28 GiB.


## Sharp actual pair-target deficit and triple cancellation

Article Proposition11.1, Theorem11.2 and Proposition11.3 now
have every literal source conclusion proved CONDITIONALLY on the
already inventoried normalized-curve and ordinary/chosen-source
surface-cover properties. Their ledger status moves from
in_progress to conditional. No target deficit, incompatible
activity, repeated-index estimate or cumulant comparison is an
external premise. Unconditionally proved numbered coverage stays
81/167. P1-MATH-0119 records an unconditional strengthening of
the compressed source/target host count, bringing the confirmed
improvement total to119 without a manuscript conclusion error.

CompressedChannelTargetHosts works at arbitrary fixed positive
coefficients0<a<=b. It extends the earlier principal-channel
geometry beyond b<=4: actual compressed values have height
between N/2 and3bN, width at most b(L+1) about their actual
anchor, and the anchor is at most3bN. For each pair of actual
unit offsets(i,j), the map((x,y),z) -> (anchor(x,y),z) is
injective. Exact source-space compression identifies the
nonzero target intersection with a genuine dependent pair of
finite effective blocks. The existing complete article10.3
then counts these pairs, including the diagonal where z equals
the compressed anchor. No private prime, local full rank,
compatibility, separation or pair injectivity is required.

CompressedChannelTargetCount.fixed_offsets has a common
critical-band threshold before all actual unit offsets.
Summing the actual finite offset cover and absorbing its
(L+1)^2 multiplicity gives the unconditional bound
#allTargets(N,a,b,L)<=N^(1+epsilon).
The actual tuple population includes every source with at
least one exact normalized coincidence and every target whose
effective space meets the original pair sum nontrivially.
The fixed coefficients need not be coprime or distinct.
This weaker-assumption count is P1-MATH-0119. It does not
assert the private-channel probability bound for arbitrary
nonprivate sources, or improve a printed asymptotic exponent.

PairTargetCost defines the actual restricted pair/target mass
and actual incidence population. It proves their exact
weighted-sum identity and monotonicity in both the pair family
and the ground set, retaining all covariance signs by absolute
value and every heterogeneous target marginal. The original
deficit is exactly this mass on the actual dependent-pair
family. The already constructed three-class channel partition
therefore gives an exact three-term deficit decomposition.
Every actual private-pair/target incidence belongs to the image
of the actual compressed tuple population; counting an image
costs no orientation or inverse-normalization assumption.

ChannelPairTargetCost.uniform_channel combines that proved
N^(1+epsilon) population count with the actual private-pair
coefficient cap N^(-2+1/b+epsilon) and the actual target cap
K_C/N. It proves the total actual pair/independent-target
cost N^(-2+1/b+epsilon), uniformly before EVERY prime cutoff H.
Its fixed finite private-channel union therefore costs
N^(-5/3+epsilon). Affine incompatibility is allowed in this
positive absolute cost. A separate uniform_restricted_mass
bounds any actual pair subfamily by its own absolute activity
times N^(-1/2+epsilon), using the already complete fixed-source
independent-target mass theorem. These finite arithmetic
source/target counts and channel-cost bounds are unconditional.

SharpPairTargetDeficitUnderInputs.article_11_1 chooses the
finite-channel partition with a small fixed fraction of the
final margin. The good part has the stronger5/3 rate just
proved; the weak and exceptional parts each have3/2 rate
from their actual activity and the independent-target half
count. Their exact sum and constant absorption prove
D_(2,1)(G)<=N^(-3/2+epsilon) for every deterministic subset G
of the original dyadic block, not only the positive-marginal
ground set. The same threshold also gives
A2(G)<=N^(-2/3+epsilon). The exact geometric source cap is
epsilon/512. It is fixed before the actual source/target
populations and is not a deficit estimate supplied as an input.

SharpThirdCancellationUnderInputs.uniform_cancellation uses
that proved deficit and the unconditional incompatible-triple
reduction. For every actual positive-marginal ground subset G,
it proves simultaneously
  incompatible absolute triple activity<=N^(-3/2+epsilon),
  0<=A3-K3plus<=N^(-3/2+epsilon),
  |kappa3-6K3plus|<=N^(-3/2+epsilon),
  absolute repeated-index cost<=N^(-5/3+epsilon).
Both signs of incompatible coefficients remain in the sum.
Every repeated occurrence of a Bernoulli variable is retained;
the stronger5/3 repeated-index rate is derived from the actual
marginal caps and sharp A2 estimate, not assumed. The exact
connected_activity_eq identifies the full absolute triple sum
with the literal connected A3 in the source. Compatible
coefficient nonnegativity was already proved unconditionally.
The geometric source cap is preciselyepsilon/2048 in this
joint theorem, with one threshold before G,N,L. Its actual
positive-marginal premise is the source admissible set, not a
homogeneous or regular-window replacement.

Stable input P1-ARITH-COMPRESSED-CHANNEL-TARGETS is now proved.
The only unproved properties in the final three article rows
remain P1-GEO-NORMALIZED-CURVE-UNIFORM,
P1-GEO-ORDINARY-SURFACE-COVER and
P1-GEO-CHOSEN-SOURCE-SURFACE-COVER, as ordinary explicit theorem
arguments at the displayed finite caps. This checkpoint adds
no new literature assumption, Paper C source, kernel axiom,
dependency download or manuscript-byte edit. It does not prove
the remaining dense primitive triple bound, the optimal third
cumulant exponent/lower bound, conditional Palm rates or any
complete count-law reconstruction. Palomar remains deferred.

Verified under Lean v4.36.0-rc2: full build passed (12931 jobs); direct axiom audit passed for 9593 declarations using only propext, Classical.choice and Quot.sound; all 7738 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.24 GiB.


## Complete several-small-kernel window lemma

Article Lemma 15.4 is complete, with both literal source clauses
proved unconditionally for the actual complete dyadic windows.
It moves from not_started to proved. Numbered coverage is now
82/167. Confirmed mathematical improvements total 120; finding
P1-MATH-0120 records the endpoint A=2 and the weaker parameter
hypotheses actually proved. No source conclusion error is claimed.

CutoffSquareParts defines the full small-prime part s_Y(n), the
literal large square part a_Y(n)=product_(p>Y) p^(valuation_p(n)/2),
and d_Y(n)=s_Y(n)*a_Y(n)^2. This a_Y is not replaced by the
all-prime canonical square part. The exact decomposition
n=d_Y(n)*K_Y(n), quotient identity d_Y=n/K_Y, positivity and
divisibility are proved. Prime divisors of the small part are
at most Y; prime divisors of the large square part exceed Y
and divide n. Large square parts of distinct values at distance
at most Y are therefore coprime. Their coprimality with every
small part proves the exact lcm identity
lcm_i d_Y(v_i)=(lcm_i s_Y(v_i))*product_i a_Y(v_i)^2.
No squarefree replacement of these full prime powers is used.

PrimePowerAllocations assigns each complete prime power of a
positive modulus to one actual selected value that contains it.
Existence of that value follows from the factorization maximum
formula for a finite lcm. The resulting factors are pairwise
coprime, divide their actual values and have exactly the modulus
as product. This gives an actual SmoothModulusHosts certificate
whenever the modulus divides the lcm of actual positive values.
The construction does not assume a squarefree modulus or an
arithmetic assignment/count estimate.

ProductFirstPassage proves finite first-crossing statements for
indexed integer factors and for a factor list with a prescribed
initial product. Its smooth variant retains prime factors with
their multiplicities. SmallKernelCrossingCertificates applies
these to the actual quotients at bounded injective offsets.
If their lcm exceeds X and each a_Y(v_i)^2<=Z, it constructs
either a genuine square r^2 with X<r^2<=X*Z, or a genuine modulus
d with X<d<=X*Y and K_Y(d)=1. Each output carries the actual
pairwise-coprime CRT factors dividing the actual nearby values.
In the second branch, the complete product of large square
parts is kept as the initial product; only small-prime factors
are added. No ambient vector space or target counting assertion
is supplied as a premise.

SmallKernelLcmGrowth proves that m actual kernels at most N^beta
force the quotient lcm above C*N, for every fixed C>=0, when
m*(1-beta)>1. Each quotient is bounded below by a fixed positive
multiple of N^(1-beta). Its actual pairwise gcd is at most twice
the offset width. The finite product/lcm inequality and a proved
polylogarithmic absorption estimate give the strict growth.
The common threshold precedes the cutoff, width, centre and
every actual selected offset family. This is an unconditional
arithmetic estimate, not a quoted asymptotic input.

SquareCertificateCount counts the actual centres from square
certificates by enumerating their roots. The old fixed-modulus
CRT bound and the proved divisor subpower estimate absorb all
complete-prime-power allocations and bounded offsets. It has
one common threshold before the finite centre population and
all widths/interval endpoints. The already proved
SmoothCertificateCount counts the other branch: K_Y(d)=1
allows a Y-smooth factor times a square, with no requirement
that d itself be Y-smooth or squarefree.

SeveralSmallKernelCount combines these two actual populations
at X=2N. The square modulus has root at most
2*N^((1+u)/2) and polynomial height at most N^3 when u<=1.
The other modulus is at most 2*N*(log N)^A. Their union has
cardinality at most N^(max(1-1/A,(1+u)/2)+epsilon).
The selected offsets can vary with each actual centre after
the common threshold. No finite centre count is assumed.

SmallKernelWindowSets defines the actual small-value set inside
NormalizedWindowSets.values(x,L)=[x-1,x+L), the corresponding
severalWindows set and the actual twoWindows product-kernel set.
Finite subset selection gives m distinct actual values and
their bounded injective signed offsets. SmallKernelWindows
then proves the several-window count at the literal cutoff
floor((log N)^A), which represents exactly the primes above
the real threshold (log N)^A. On the critical band, this cutoff
eventually exceeds twice the complete window width. The second
source clause follows from the already proved actual two-kernel
product-cap count, at every H<=D*(L+1). It has the bound
#twoWindows<=N^(q+epsilon), simultaneously for every real q.
The joint theorem article_15_4 supplies one threshold before
every critical length, H and q. The source q>=0 is included.

The endpoint A=2 is covered: the square-smooth Rankin input
allows every sigma>1/2, hence the same N^(1/2+epsilon) modulus
count there. The several-window theorem only needs u<=1 and
m*(1-beta)>1; it uses no positive lower bound on beta or u.
These are the exact proved improvements in P1-MATH-0120.
For negative exponents, an impossible actual selection is
handled by the same statement rather than an omitted case.

This checkpoint adds no external literature property, Paper C
port, kernel axiom, dependency download or manuscript-byte edit.
It does not prove the separate sharp individual two-kernel
7/12 estimates in companion T1.5/T1.13, the Reuss-based input,
or the remaining primitive-mass and count-law reconstruction
results. Existing geometric conditional statements retain their
explicit unproved properties. Palomar remains deferred.

Verified under Lean v4.36.0-rc2: full build passed (12953 jobs); direct axiom audit passed for 9645 declarations using only propext, Classical.choice and Quot.sound; all 7799 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.20 GiB.


## The rational witness survives in the full third cumulant

Article Proposition14.5 now has every literal conclusion proved,
conditionally on exactly the previously inventoried normalized-curve
and ordinary/chosen-source surface-cover properties. Its status moves
from in_progress to conditional. The actual positive connected
lower bound remains unconditional. Numbered unconditional coverage
stays82/167 and confirmed mathematical improvements stay120.

SharpThirdCumulantLowerUnderInputs.article_14_5 applies the already
proved sharp third-cumulant cancellation at the fixed margin1/15.
Its error is N^(-43/30), whereas the actual rational witness family
gives K3plus>=c(C)*N^(-41/30), with the explicit positive
c(C)=2^(-4-(71/30)*C)/240. A proved constant-absorption estimate
bounds the error by c(C)*N^(-41/30) eventually. Therefore the full
third factorial cumulant is at least5*c(C)*N^(-41/30).
The factor5 is a convenient checked lower constant, not a sharp
leading coefficient. Every covariance sign, incompatible triple
and repeated occurrence is already included in the cancellation
theorem; none of these terms is discarded in the lower bound.

The joint theorem simultaneously supplies the lower bound for
K3plus on the actual positive-marginal ground set, for its third
factorial cumulant, and for the third factorial cumulant of the
full original dyadic count. The last equality uses the proved
exact restriction of all factorial moments to positive marginals.
It does not discard an exceptional-window event. The common
threshold precedes every critical length. All geometric inputs
are ordinary explicit theorem arguments, at the single fixed
source-cover cap GeneralGraphHostCount.sizeCap(1/30720), and
the corresponding explicitly displayed finite degree bounds.

No target cumulant lower bound, error estimate, arithmetic
exception count or rational witness density is assumed. There
is no new literature property, kernel axiom, dependency download,
Paper C port or source-manuscript edit. This does not complete
the sharp upper bound for the third cumulant or the remaining
aligned/primitive triple populations in article14.1/14.3/14.6.
Palomar remains deferred until the complete project is verified.

Verified under Lean v4.36.0-rc2: full build passed (12955 jobs); direct axiom audit passed for 9647 declarations using only propext, Classical.choice and Quot.sound; all 7801 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.18 GiB.


## Actual two-target sections and separate coordinate budgets

The effective linear-algebra and separate coordinate budgets in
the proof of article Lemma15.2 are now proved unconditionally.
Its status moves from not_started to in_progress. This is a
preparatory checkpoint: neither the actual dense-pair host count
nor its weighted mass estimate is complete. Numbered completed
coverage stays82/167; confirmed mathematical improvements stay120.

TwoTargetKernel works over an arbitrary field. Its relation space
is the genuine kernel of addition W x Y x Z -> ambient space,
with effective subspaces W,Y,Z. Disjointness W/Z proves that
projection to Y is injective; disjointness W/Y separately proves
that projection to Z is injective. There is no disjointness premise
between the two targets. Rank-nullity gives exactly the printed
dimension deficit, and the kernel dimension is at most the
minimum of the two target dimensions. No formal local rank is
substituted for an effective target dimension.

EffectiveLinearSections proves that every subspace of the range
of an actual linear map admits a genuine injective linear section.
Lifting the three entries of the relation kernel through these
sections preserves their exact sum-zero equation, together with
the separate injective target projections. The section exists
without injectivity or local full rank of the original quotient
map, and without any restriction on which effective subspace W
is chosen. No count of sections or subspaces is asserted.

TwoTargetWindowSections instantiates these facts on the literal
even-selection maps of the original source and target windows.
The source map is the sum of their actual square-class maps;
its range is precisely the sum of the source effective spaces.
Every W inside that sum has an exact source section, and each
actual target has its own even-selection section. The resulting
physical lift keeps every source and both target coordinate
blocks, every block has even total parity, and the full actual
prime-parity vector sum is zero. Both target projections into
their own L+1 physical coordinates remain injective. The actual
kernel dimension is at most L. No positivity, pair separation,
source distinctness, affine compatibility, or regular-window
assumption is required for these algebraic statements.

SimultaneousProjectionRegularization chooses ONE recovery
subspace for an arbitrary family of injective coordinate
projections. The same codimension loss bounds each projection's
distinct nonzero label count separately; it is not just a count
for their union. The recovery multiplicity and physical support
pool bounds hold on that same subspace. No number of target
projections is inserted into the loss. This theorem is then
applied to the two actual target lifts.

TwoTargetRegularization.uniform_regularization chooses its fixed
recovery order from s and xi BEFORE every source tuple, both
target centres, the length and W. It produces the actual three
sections and one shared M. Its codimension is at most xi*L/4;
each target separately has at least dim(R)-xi*L/4 distinct
nonzero coordinate labels. The source sum W is arbitrary inside
the fixed sources, including on irregular windows. Every exact
prime equation is retained by the physical lift. The actual
support pools have the proved fixed bound
supportBound(s+1,t,t-1), not an assumed arithmetic enumeration.

TargetComponentBudget proves finite geometric-free counting
facts for disjoint physical sets. Distinct nonzero target labels
are at most the number of monochromatic pieces meeting that
target. For any disjoint piece family C and target coordinate
set T, the exact budget is
  2*#pieces_meeting_T <= #T + #pieces_meeting_T_once.
Thus the number of singleton target occurrences is at least
2*m-#T, separately for each target. The proof counts actual
intersections; it does not require a graph without isolated
active coordinates or a count for a union of targets.

LabelClassPartition constructs the actual nonzero physical
label classes. They cover all active coordinates and are
pairwise disjoint and monochromatic. The number of classes
meeting a specified target equals its actual number of
distinct nonzero labels. Recovery multiplicity bounds every
class's size. TargetLabelsComponents links these finite sets
to actual coordinate projection rank and proves both component
and singleton budgets for any field. Finally the actual
physical_class_budgets and physical_class_size supply these
bounds on each of the two original targets of the shared M:
  m_j >= dim(M),
  2*dim(M) <= L+1+n_(1,j),
  every nonzero physical label class has size <=t-1.
The classes are explicitly constructed. No physical partition
or target count is supplied as an external premise.

The arithmetic coefficient enumeration for two free targets,
the removal of weak aligned alternatives, the two dense rank
strata and their final weighted summation still require proof.
The label-class partition alone is not claimed to supply the
component equations or the final geometric host bound.
Accordingly this checkpoint does not close article15.2 or15.3,
and it adds no numbered completion or new finding identifier.
There is no new literature assumption, kernel axiom, Paper C
port, dependency download or source-manuscript edit. Existing
geometric conditional properties and Palomar status are unchanged.

Verified under Lean v4.36.0-rc2: full build passed (12971 jobs); direct axiom audit passed for 9691 declarations using only propext, Classical.choice and Quot.sound; all 7863 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.16 GiB.


## Actual common coefficient pool for two free targets

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

Verified under Lean v4.36.0-rc2: full build passed (12989 jobs); direct axiom audit passed for 9722 declarations using only propext, Classical.choice and Quot.sound; all 7911 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.13 GiB.


## Effective recovery subspaces and literal two-target coefficients

The actual effective-kernel regularization in article15.2 now
passes to a genuine subspace P of the literal physical window
code. Its dimension loss remains measured in the EFFECTIVE
relation kernel, and both target projections stay injective.
This completes the algebraic/arithmetic bridge to the previously
proved common source coefficient pool. The dense pair geometric
selection, weak-alignment removal and weighted summation remain
open. The numbered coverage stays82/167, and the121 confirmed
mathematical improvements are unchanged.

RecoveryImage proves that intrinsic NoDisjointRecovery transfers
through any injective linear map, using the actual equivalence
from a subspace to its image. Nonzero dual labels pull back to
nonzero labels; every recovery equation pulls back literally.
The image has the same finite rank, and injective target
projections transfer through their exact commuting squares.
These statements work over any field.

TwoTargetCodeLift puts the actual three-section physical lift
inside PhysicalWindowRelations.code. The membership proof uses
the already verified even parity in every physical block and
the exact zero sum of all prime-valuation vectors. Each target
projection commutes with this lift and every code coordinate
form pulls back to the corresponding effective-kernel form.
Injectivity of either target projection proves injectivity of
the complete lift. No injectivity of a local square-class map,
target disjointness, regular window or chosen-basis count is
assumed.

TwoTargetIntrinsicClassCoefficients and TwoTargetIntrinsicEnumeration
strengthen the previous coefficient theorems: only intrinsic
NoDisjointRecovery is needed. The proof reconstructs coordinate
multiplicity and bounded support pools from that condition.
It does not require a codimension bound measured in the entire
physical code. This distinction matters for irregular windows:
the full physical code contains local relations that are absent
from the effective kernel, so an image's codimension there need
not equal its regularization loss. No such equality is asserted.
The source cover cardinality, full squarefree coefficient,
common N^epsilon pool, positive polynomial coefficient height
and actual integer square equation all remain unchanged.

TwoTargetPhysicalRegularization chooses t from s and xi before
every source tuple, both targets, L and W. It then produces the
image P of the SAME effective recovery subspace, with intrinsic
recovery exclusion, dim(P)>=dim(R)-xi*L/4 and two injective
literal target-coordinate projections. P's rank is proved equal
to the effective subspace rank through the image equivalence.
No second restriction of the relation space is made.

TwoTargetPhysicalBudgets supplies the actual nonzero coordinate
class partition on P. Every class has at most t-1 coordinates;
separately for j=0 and j=1, its classes satisfy
  #classes_meeting_target_j >= dim(P),
  2*dim(P) <= L+1+#classes_meeting_target_j_once.
These are consequences of the proved target injections and
the actual class partition, not assumed density premises.

TwoTargetPhysicalEnumeration.uniform_enumeration finally fixes
t before D,C,epsilon and the asymptotic threshold. For every
source tuple in the critical dyadic band, its one coefficient
list has at most N^epsilon entries. For every actual target
pair and arbitrary W inside the source sum, disjoint from each
target separately, it constructs the physical P above. EVERY
nonzero label on P has its actual full target-product kernel
in that SAME source-only list, positive and at most N^(2*(t-1)),
and multiplying the literal target product by it is an integer
square. Thus no enumeration of sections, recovery subspaces
or targets is inserted into the coefficient budget.

The source dimension deficit is still the genuine effective
one, including on irregular windows. This is an unconditional
internal bridge, not the full conditional dense-pair estimate.
There is no new literature input, mathematical-finding number,
kernel axiom, Paper C port, dependency download or source edit.
Palomar remains deferred.

Verified under Lean v4.36.0-rc2: full build passed (13003 jobs); direct axiom audit passed for 9738 declarations using only propext, Classical.choice and Quot.sound; all 7928 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.10 GiB.


## Actual mixed-class equations and nonaligned half-power hosts

The mixed, nonaligned geometric branch of article15.2 now
uses literal physical label classes and their actual source
coefficient list. The branch proves a uniform N^(1/2+epsilon)
bound when a fixed number of distinct nonzero classes each
meet BOTH targets. Its only unproved inputs are the existing
chosen-source surface-cover and normalized-curve properties,
as explicit theorem arguments. The pure-class alternative,
weak aligned pairs, upper singleton stratum and final weighted
dense mass are still open. Main15.2 remains in_progress;
unconditional numbered coverage82/167 and121 improvements
are unchanged.

CoefficientSplitRadicalPatterns enumerates bounded integer
offset sets and a fixed number of entries from ANY actual
finite positive coefficient list Q. It does not require these
coefficients to have only small prime factors. Its exact finite
cardinality is the old proved offset-pattern cardinality times
|Q|^k. CriticalCoefficientPatterns chooses the explicit positive
coefficient margin epsilon/(2*(k+1)); a list of that subpower
size and all offset patterns together cost at most N^epsilon
on the critical band. One threshold precedes every list Q.

CoefficientNonalignedHostCount applies the already proved
general integer-root host theorem for polynomial-height
coefficients. A finite cover over the ACTUAL pattern pool
then sums all root-system counts. This gives N^(1/2+epsilon)
for arbitrary positive coefficient lists with their explicit
small cardinality and height bounds. Offset sets can have
unequal degrees in different equations; they must be disjoint
within each target and nonempty in both targets. Literal
CompressedTargetAlignment nonalignment is retained, rather
than silently inferred for weak aligned pairs. The selected
homogenization and equation count precede the geometric inputs
and every N,L,Q and host set.

TwoTargetClassOffsets constructs the ACTUAL indices and integer
offsets of a physical class in each of the two target blocks.
Its target coordinate images partition precisely the nonsource
coordinates of the class. The two images are disjoint; their
offset cardinalities add to at most the physical class size.
Different classes have disjoint offsets separately in each
target. Each offset has absolute value at most L+1. The exact
integer product is proved equal to the previous literal
targetProduct, so its square equation gives actual integer
roots of the split product at the two target centres. These
are constructed data, not root equations postulated as inputs.

TwoTargetMixedClassData restricts the source-only coefficient
list to positive entries at most N^(2*(t-1)). This only decreases
its cardinality and retains EVERY actual nonzero class
coefficient, by the previously proved enumeration. Given any
fixed number of distinct nonzero mixed classes on an actual
intrinsic-recovery subspace M of the literal code, it constructs
one admissible bounded-coefficient pattern and all its integer
square roots. Both within-target disjointness conditions and
the total degree bound t-1 follow from the actual class
partition and recovery multiplicity. The enumeration threshold
precedes even this chosen equation count.

TwoTargetNonalignedMixedCount.uniform_hosts now supplies the
literal arithmetic branch: fix s,t,D,C,epsilon, choose the
geometric degree and number k of equations, then supply the
two existing uniform geometric properties. A common A and N0
bound EVERY finite set of actual dyadic target pairs above
EVERY actual fixed source tuple, whenever the pairs are
nonaligned and possess an actual intrinsic-recovery subspace
with k distinct nonzero classes meeting both targets. It gives
|F|<=A*N^(1/2+epsilon). The source coefficient pool, positivity,
polynomial height, offset patterns and roots are all internally
constructed. No pair host bound, assumed pattern enumeration,
subspace count or regular-window condition is an external
premise. This proves one branch of the dense-pair argument;
the assertion that density forces either that branch or the
univariate alternative is not yet supplied by this checkpoint.

The geometric inputs have the exact forms
UniformSourceSurfaceCover.UniformCover k (t-1) Ds and
UniformNormalizedCurvePointCount.UniformBound
((Ds+2).choose2+k) M for every M. Their standard identifiers
P1-GEO-CHOSEN-SOURCE-SURFACE-COVER and
P1-GEO-NORMALIZED-CURVE-UNIFORM remain unformalized literature
inputs. They are ordinary explicit arguments, never kernel
axioms. No new literature claim, finding, dependency download,
Paper C port or source-manuscript edit is made. Palomar remains
deferred.

Verified under Lean v4.36.0-rc2: full build passed (13015 jobs); direct axiom audit passed for 9766 declarations using only propext, Classical.choice and Quot.sound; all 7965 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.07 GiB.


## Complete lower nonaligned dense-pair cardinality stratum

The complete LOWER nonaligned cardinality stratum in article15.2
is now proved conditionally on the existing two explicit
chosen-source geometric properties. For arbitrary fixed actual
sources and arbitrary W inside their effective sum, the literal
dyadic nonaligned pairs with W disjoint from each target and
effective relation dimension at least eta*L have cardinality
O(N^(1/2+epsilon)). The dimension condition now internally
produces either enough mixed classes or two pure classes for
each target. It is not an assumed geometric host-count premise.
The upper singleton stratum, weak aligned pairs and weighted
dense mass remain open, so main15.2 stays in_progress. Coverage
remains82/167 and confirmed improvements remain121.

CoefficientUnivariateCount proves an unconditional pooled
one-variable count. Two actual NONEMPTY DISJOINT bounded
offset equations with positive integer coefficients from one
small common list have at most N^epsilon critical dyadic hosts.
This uses the previously proved DisjointSquareEquations bound;
no coefficient height or external curve estimate is needed for
this univariate branch. The pool of all bounded offset patterns
and pairs of coefficients costs the explicitly allocated
subpower margin. The threshold precedes every list, offset
pattern and host set. Counting both coordinate projections
then gives at most N^epsilon ordered pairs when each centre
has such a two-equation system from that SAME list. Correlation
between the chosen systems is allowed.

TwoTargetLabelSelection constructs the actual nonzero labels
in each target and their mixed intersection and pure differences.
Membership is proved equivalent to the corresponding physical
class meeting that target. A pure label has an EMPTY offset
set in the other target. An explicit finite-sampling theorem
selects distinct labels from any sufficiently large finite
population. If each target has at least k+2 labels, either k
distinct mixed labels can be selected, or two distinct pure
labels can be selected separately for EACH target. This is an
exact finite cardinality argument; no density assertion or
number of subspaces is supplied as an input.

TwoTargetPureClassData rewrites the previously proved literal
target-product square equation of a pure class to a genuine
one-variable equation: the other target's integer product is
the empty product one. Two distinct pure classes have disjoint
offsets in the chosen target. Their size and coefficient list
are supplied by intrinsic recovery and the actual common source
enumeration. For both target orientations, the actual system
is constructed, with all square conditions proved. A common
critical threshold precedes every actual source tuple, target
pair, recovery subspace and choice of the two labels.

TwoTargetPureCount.uniform_pairs proves the full PURE branch
unconditionally: any finite dyadic target-pair set admitting
these actual two pure classes in each target has at most
N^epsilon entries. The coefficient list depends only on the
fixed sources. Positivity and its subpower cardinality are
proved internally. There is no alignment, local regularity,
target disjointness or geometric literature hypothesis in this
pure-class theorem. The subspace and labels may vary with each
actual target pair.

TwoTargetLabelDimension explicitly identifies each target's
label population with its physical-class count, so the proved
injective projection gives dim(P)<=#target_labels separately
for the two targets. Both counts use the SAME actual P.

TwoTargetNonalignedDenseCount.uniform_pairs combines ALL these
steps. It first fixes the recovery parameter from s and eta,
then the chosen-source surface degree and number k of equations,
then takes exactly the existing surface-cover and normalized
curve properties as ordinary explicit arguments. It chooses a
uniform length threshold before every source tuple and W.
For every actual pair with d>=eta*L, effective regularization
gives dim(P)>=d-eta*L/4. On the critical band this exceeds k+2
for all sufficiently large N. Separate target injections and
the exact label dichotomy therefore give the actual mixed or
pure alternative. Partitioning the actual host set by mixed
existence, the mixed part has O(N^(1/2+epsilon)) cardinality
and the remaining pure part has at most N^epsilon cardinality.
Their sum gives the claimed bound with an explicit enlarged
constant. Sources and W are arbitrary, and irregular windows
remain included via the exact effective sections.

This theorem uses the genuine kernel dimension. The earlier
effective_dimension_formula proves that it is exactly the
printed dim(W)+dim(S_y)+dim(S_z)-dim(W+S_y+S_z), rather than
the full physical relation rank with local kernels. The
statement allows any finite set of the actual qualifying
dyadic pairs; source freshness and distinctness can be imposed
by taking a subset. No weighted mass estimate is claimed.

The two external properties retain their previous exact forms:
UniformSourceSurfaceCover.UniformCover k (t-1) Ds and
UniformNormalizedCurvePointCount.UniformBound
((Ds+2).choose2+k) M for every M. No new literature input,
kernel axiom, mathematical-finding identifier, Paper C port,
dependency download or manuscript source edit is introduced.
The full article15.2 conclusion and Palomar remain deferred.

Verified under Lean v4.36.0-rc2: full build passed (13027 jobs); direct axiom audit passed for 9779 declarations using only propext, Classical.choice and Quot.sound; all 7985 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.03 GiB.


## Complete upper nonaligned dense-pair cardinality stratum

The complete UPPER nonaligned cardinality stratum in article15.2
is now proved under the existing explicit ordinary-surface and
normalized-curve properties. Actual nonaligned dyadic pairs
whose effective relation dimension is at least (1/2+delta)*L
have O(N^epsilon) cardinality, uniformly over arbitrary fixed
sources and W inside their effective sum and disjoint from each
target separately. Together with the preceding lower count,
this verifies both nonaligned cardinality strata. Weak aligned
pairs and the final weighted and source-restricted statements
remain open, so main15.2 stays in_progress and numbered proved
coverage stays82/167. P1-MATH-0122 records the direct whole-label
class proof of these nonaligned strata, bringing confirmed
mathematical improvements to122.

CoefficientDegreeOneHostCount pools the actual degree-(a,1)
integer-root systems over any common small positive coefficient
list of fixed polynomial height. Every pattern may have its own
positive degree a, but within one selected system that degree
is fixed. The singleton offset in the second target is actually
constructed from its one-element set; within-target disjointness
proves the singleton offsets are distinct. The already proved
literal degree-one count then applies. Ordinary affine-curve
counting is obtained by the proved ordinary_specialization of
the normalized-curve property, rather than introduced as another
external premise. A positive fixed equation count is chosen
before all geometric inputs, coefficient lists and hosts.

TwoTargetSingletonLabels identifies each physical target's
singleton classes with their distinct nonzero labels. It proves
the exact image identity, cardinality equality and membership
criterion for these actual labels. The previous physical
projection budget therefore becomes, separately in each target,
  2*dim(P)<=L+1+#singleton_labels_j.
The classes and their cardinalities are literal physical sets.

TwoTargetSingletonSelection proves the actual finite dichotomy.
With class size at most K, if each target has at least
(K+1)*k+2 singleton labels, either one orientation supplies k
distinct mixed labels of one common positive other-target
degree, or two pure labels are available in EACH target.
The fixed type is chosen by a finite pigeonhole argument on
degrees0,...,K. Its degree is positive because the selected
classes really meet the other target and k>=1. No type,
population bound or pure/mixed alternative is assumed.

TwoTargetSingletonClassData constructs both orientations of
the actual degree-one square system. Its coefficients are the
same full squarefree target-product kernels from the source-only
list, and its offset sets are those of the actual classes.
The product equation is transported exactly, including the
commutative product reordering needed when the first target is
the singleton side. Degree, disjointness, bounded offsets and
all integer roots are internally proved. One threshold precedes
every actual target pair, subspace, number of equations and
choice of the singleton orientation.

CompressedAlignmentSymmetry proves the exact source alignment
relation symmetric for a fixed width multiplier. Consequently
TwoTargetNonalignedSingletonCount applies the same geometric
bound to either target orientation, with an explicit injective
integer host map. Both orientations share one constant and
threshold. A pair's positive other-target degree and actual
recovery subspace may vary with that pair; the common source
coefficient budget remains uniform. Its result is O(N^epsilon)
for every actual nonaligned host set with the selected mixed
singleton configuration.

TwoTargetNonalignedUpperCount.uniform_pairs closes the entire
upper nonaligned count from the genuine dimension hypothesis.
Choose the recovery parameter from s and delta before every
source and target. Regularization retains
dim(P)>=d-delta*L/4. For d>=(1/2+delta)*L the separate target
budgets imply at least (3*delta/2)*L-1 singleton labels in EACH
target. At one common critical length threshold these exceed
t*k+2, which is precisely the finite selection threshold for
K=t-1. The proved dichotomy gives one of the two orientations
of the mixed degree-one branch or the unconditional pure
branch. A finite cover of the actual host set by these three
actual populations gives O(N^epsilon), with no enumeration of
subspaces, sections, deletion patterns or prime assignments.

The effective kernel dimension is used throughout; no full
physical local kernel is added. Irregular windows, overlapping
targets and arbitrary W inside the actual source sum are
allowed. The nonalignment condition is retained literally.
These results do not remove the small aligned curves for weak
aligned pairs. Nor do the cardinality estimates themselves
establish the weighted sum in the source lemma. Both tasks
remain explicitly open in the result ledger.

The exact upper-branch external properties are
UniformOrdinarySurfaceCover.UniformCover k (t-1) and
UniformNormalizedCurvePointCount.UniformBound (k+3) M for all M.
These are the previously recorded P1-GEO-ORDINARY-SURFACE-COVER
and P1-GEO-NORMALIZED-CURVE-UNIFORM. The lower mixed branch
retains the existing chosen-source surface property. There is
no new unformalized literature input or kernel axiom, Paper C
port, dependency download or original manuscript-byte edit.
Palomar remains deferred.

Verified under Lean v4.36.0-rc2: full build passed (13045 jobs); direct axiom audit passed for 9791 declarations using only propext, Classical.choice and Quot.sound; all 8001 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 14.00 GiB.


## Literal nonaligned dense-pair mass above arbitrary effective sources

The full literal NONALIGNED weighted summand of article15.2
is now proved conditionally on the three existing geometric
properties. The theorem uses the exact actual heterogeneous
infinite-model marginals, the printed effective dimension
deficit, distinct target centres and exclusion of all fixed
source centres. It proves the N^(-1+epsilon) bound with one
threshold before every source tuple and W. Weak aligned pairs
and the full source-restricted primitive-family clause remain
open, so main15.2 stays in_progress. Proved numbered coverage
remains82/167 and confirmed improvements remain122.

TwoTargetNonalignedRankWeight proves the complete effective
rank-weight sum O(N^(1+epsilon)) over EVERY finite set of
actual qualifying nonaligned dyadic target pairs. It partitions
the actual set at d=(1/2+delta)*L. The previously proved lower
cardinality estimate and a proved critical binary-power bound
pay for the lower stratum. The upper cardinality estimate
and the genuine effective inequality d<=L pay for the upper
stratum. All internal margins are fixed before N. The two
regularization parameters and geometric equation counts are
chosen before the sources and W; they may differ between the
two strata. No abstract rank-weight bound is assumed as input,
and no physical local kernels are added to d.

TwoTargetNonalignedMass.uniform_mass multiplies this rank sum
by the proved uniform cap on the EXACT actual marginals.
Their nonnegativity and separate bounds give
p_y*p_z<=(M/N)^2, retaining all incompatible and irregular
windows as their actual probabilities dictate. Finite sums
are handled exactly, then the fixed multiplicative constant
is absorbed into the remaining exponent margin. The result is
sum(p_y*p_z*2^d)<=N^(-1+epsilon), uniformly over the actual
sources and every W inside their effective sum, when W is
disjoint from each target and d>=eta*L. There is no replacement
of the marginals by a homogeneous probability or assumption
of compatibility.

TwoTargetDensePairs defines the literal nonaligned population:
both centres lie in the dyadic block, are distinct and outside
every prescribed source centre, are nonaligned in the source's
exact sense, and satisfy the separate W disjointness and
effective density conditions. Its explicit deficit is
dim(W)+dim(S_y)+dim(S_z)-dim(W+S_y+S_z). The earlier exact
effective dimension formula proves this equals the actual
relation-kernel dimension for every W inside the source sum.
The membership equivalence records every restriction.

TwoTargetNonalignedMassTheorem.article_15_2_nonaligned now
states and proves the actual printed weighted nonaligned
summand on that explicit finite population, with the printed
deficit in both its membership condition and exponent. It
does not merely apply to an unspecified host set. The fixed
source tuple and W can be irregular or dependent; their
admissibility is precisely W<=sum(source spaces), with the
separate target disjointness imposed on the summation set.

The exact external arguments remain the existing chosen-source
surface cover for the lower mixed stratum, the ordinary surface
cover for the singleton stratum and normalized-curve bounds in
their two explicit ambient dimensions. These are the same
three recorded P1-GEO identifiers, without a new unformalized
input. Their translation from the literature is still open;
they remain ordinary explicit theorem parameters, not axioms.

This closes the nonaligned weighted part only. No theta for
weak aligned pairs, removal of their small curves, or full
source-restricted primitive dense mass is claimed. Those
unproved portions prevent completion of article15.2. There
is no new mathematical-finding number, Paper C port, dependency
download or original manuscript edit. Palomar remains deferred.

Verified under Lean v4.36.0-rc2: full build passed (13053 jobs); direct axiom audit passed for 9796 declarations using only propext, Classical.choice and Quot.sound; all 8008 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 13.97 GiB.


## Actual units and fixed selected grids for weak aligned targets

The arithmetic foundations for the weak aligned selection
stage of article15.2 are now proved unconditionally. Actual
units have the claimed lower effective intersection rank,
all but one unit can be excluded through boundedly many actual
coordinate labels, and the surviving fixed-size normalized
selections give the exact even independence and disjointness
required by the existing geometric host theorems. The remaining
population budgets after exclusion and their geometric host
count composition are not yet complete. Main15.2 remains
in_progress;82/167 proved numbered results and122 confirmed
mathematical improvements are unchanged.

EvenImageEmbeddingDefect uses the previously proved actual
extension by zero along a finite embedding. It constructs an
injective map from the selected even-map kernel into the full
even-map kernel and proves the finite-rank inequality. Over
any division ring, with no finite-dimension assumption on the
ambient value space, the selected image loses at most the
full image's defect from its formal even-selection dimension.
The outside-image zero evaluation is also proved. These are
actual maps and rank-nullity arguments, not assumed quotient
injectivity.

EvenSubsetRankDefect instantiates this on literal arithmetic
value sets S<=T:
  |S|-1<=rank(space(S))+(|T|-1-rank(space(T))).
UnitIntersectionRankLower applies it to the full normalized
intersection of the two actual windows. Normalized value-set
cardinality is proved equal to the actual unit count, and its
even image lies in the genuine target intersection. Combining
with the exact local rank identity gives the general finite
inequality
  #units<=dim(S_y intersect S_z)+local_relation_rank(y)+1.
Thus a local defect at most one gives the literal u-2 lower
intersection bound used in the companion. No private-prime
condition on the normalized union or local full-rank premise
is used. WeakAlignmentUnitCount then supplies one critical
threshold for EVERY actual pair and ALL positive channel
coefficients, with no height restriction. In the weak case it
gives u<=theta*L+2 from the actual effective intersection bound.

FiniteRungeIndependence first proves that absence of nonempty
even square-product subsets implies injectivity of the actual
even-selection map. The selected support and its product are
constructed from each hypothetical kernel vector. The proved
quantitative Runge theorem then rules out such a support in
[U,U+R] when its fixed cardinality is below the explicit
Runge threshold. CriticalFiniteRungeIndependence proves the
uniform consequence: for fixed K,D,J, EVERY actual set of at
most K integers in an interval of width at most D*(L+1)^J and
base U>=N/2 is even-independent on the critical band, above a
common N0. This is even independence, not an assertion that
each individual integer has a private prime or is nonsquare.

EvenIndependentIntersection proves the exact intersection
identity space(S intersect T)=space(S) intersect space(T)
under even independence of S union T. Equality of two actual
even combinations is extended into the common union, where
injectivity identifies their coefficients. Absent coefficients
vanish, so the common value is supported in the literal
intersection. Consequently normalized grids with at most one
common integer have disjoint even square-class spaces. Full
private-prime independence of the union is unnecessary for
this auxiliary identity.

CriticalAlignedSelections applies the finite Runge result to
the literal enlarged alignment coefficients a,b<=(L+1)^3.
The already proved enlarged pair geometry puts all deduplicated
normalized values in an interval of width at most6*(L+1)^4
with base at least N/2. A common threshold therefore makes
EVERY fixed-size selected normalized union even-independent,
including pairs with no exact unit and irregular full windows.
If the two selected normalized grids share at most one value,
the exact intersection identity and invariance under dilation
give even independence of each ORIGINAL selected grid and
disjointness of their ORIGINAL effective spaces. Both channel
orientations are included. No uniqueness-of-alignment assertion
or full-window independence is assumed.

TwoTargetUnitExclusion constructs the actual two physical
endpoints of each deleted unit and their coordinate-label
image. At most2*#deleted_units labels are excluded. Every
class with a surviving label avoids all those actual endpoints;
this removes selectable classes without restricting the
regularized relation subspace again. The exact finite
except_one construction deletes u-1 units when u>0, and zero
when u=0, leaving at most one. For selected target index sets
avoiding a deleted endpoint on each deleted unit, the literal
normalized selected value intersection has cardinality at
most one. It is covered by the image of the actual surviving
unit pairs, so no prime or alignment assignment is enumerated.

All these results are unconditional internal arithmetic and
linear algebra. They do not assume a weak aligned host count
or add an unformalized geometric input. The previously proved
nonaligned weighted clause remains complete under the recorded
geometry. To complete the weak aligned clause, the remaining
target and singleton populations after this actual label
exclusion must still be linked to the mixed/pure selection
and the existing selected-admissibility host counts. The full
source-restricted primitive clause also remains open.
No kernel axiom, new finding identifier, dependency download,
Paper C port or source-manuscript edit is added. Palomar remains
deferred.

Verified under Lean v4.36.0-rc2: full build passed (13071 jobs); direct axiom audit passed for 9820 declarations using only propext, Classical.choice and Quot.sound; all 8035 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 13.94 GiB.


## Actual selected-grid arithmetic and pooled geometric counts

The literal selected grids of actual classes now supply the
geometric admissibility needed for weak aligned targets, and
the two common-coefficient geometric counts are proved with
that selected admissibility in place of global nonalignment.
The remaining class populations after exclusion and the full
weak aligned dense host counts are still open. Main15.2 stays
in_progress, with82/167 proved numbered results. P1-MATH-0123
records the chosen-alignment finite-selection proof of this
admissibility stage, bringing confirmed improvements to123.

CoefficientPatternGrids constructs the two actual unions of
the root sets in a finite coefficient pattern. Each equation's
root sets lie in these unions, whose combined cardinality is
at most k*K when every equation has total degree at most K.
Their actual integer-value sets have no larger cardinality.
These are fixed-size selected grids, rather than full window
sets.

CoefficientSelectedHostCount proves the half-power geometric
bound after summing all bounded offset and common-list
coefficient patterns. It uses GeneralRootHostCount on the
actual selected grids, with their explicit positivity, even
independence and effective disjointness. The host need not be
globally nonaligned. These arithmetic admissibility conditions
are precise hypotheses about actual finite value sets, not an
assumed host bound. Only the existing chosen-source surface
cover and normalized-curve properties remain external inputs.

SelectedDegreeOneRootHostCount constructs the literal integer
radicand list and reindexes every root, degree and disjointness
condition. OrdinaryDyadicRootHostCount then supplies N^epsilon
hosts when the selected grids are admissible. It chooses a
positive fixed number of equations before the geometry and N.
The ordinary affine-curve input is again obtained through the
proved normalized-curve specialization. This theorem retains
polynomial-height integer coefficients and works on either
selected target orientation without a global nonalignment
premise.

CoefficientSelectedDegreeOneHostCount pools that actual
degree-one theorem over the common finite coefficient list.
A pattern's singleton right offsets are constructed and proved
distinct; its positive left degree is fixed within that pattern
and may vary across patterns. Positivity and polynomial height
of coefficients and the small list cardinality are explicit.
The resulting N^epsilon bound has one threshold before every
actual list, pattern and host set. The existing ordinary surface
cover and normalized-curve properties are its only unproved
inputs.

TwoTargetSelectedGrids identifies the actual integer offsets
of any fixed number of physical classes with the image of
their actual target indices. Their evaluated natural values
are proved exactly equal to the actual original window labels.
Both selected grids are positive and lie in their original
windows. Their total index cardinality is at most k*K. If the
physical classes avoid every endpoint of deleted actual units,
their selected indices avoid every deleted unit. The actual
normalized selected value intersection consequently has at
most one element when all but at most one unit have been
deleted. No root set, integer value or unit membership is
postulated as a geometric input.

WeakAlignedSelectedGrids.uniform_admissible finally constructs
the COMPLETE SourceCurvePointCover.Admissible property for
these actual class grids. For any supplied bounded enlarged
alignment, any fixed number of classes of fixed bounded size,
and any actual unit deletion leaving at most one unit, the
proved finite Runge independence and one-overlap intersection
identity give positivity, even independence of each original
selected grid and disjointness of their actual effective
spaces. It supplies BOTH target orientations above one
threshold chosen before all sources, targets, alignment data,
classes and deletions. The regularized relation space is not
restricted again.

This establishes the selected-admissibility mechanism needed
by the two pooled geometric host bounds. To close the weak
aligned dense estimate, the available target and singleton
label counts after deletion must still be shown sufficient,
and actual admissible patterns must be selected and counted.
The weighted weak aligned and source-restricted primitive
clauses remain unproved. There is no additional literature
input, kernel axiom, Paper C port, dependency download or
source-manuscript edit. Palomar remains deferred.

Verified under Lean v4.36.0-rc2: full build passed (13083 jobs); direct axiom audit passed for 9838 declarations using only propext, Classical.choice and Quot.sound; all 8057 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 13.91 GiB.


## Complete dense-pair first conclusion, including weak alignment

The complete FIRST conclusion of article Lemma15.2 is now
proved under exactly the previously inventoried geometric
properties. This includes the literal union of nonaligned
pairs and pairs with effective target intersection at most
a fixed positive theta*L. The printed effective deficit,
exact heterogeneous marginals, distinct targets and exclusion
of all source centers are retained. The uniform threshold is
chosen before all sources, their effective subspace W and the
targets. The source-restricted primitive-family conclusion
remains open, so main15.2 stays in_progress and unconditional
numbered coverage stays82/167. P1-MATH-0124 records the sharper
post-exclusion singleton budget, bringing improvements to124.

TwoTargetAllowedLabels removes a COMMON finite label set E
from each actual target population. Each original population
has cardinality at most the remaining population plus |E|.
Its exact mixed-or-two-pure dichotomy returns only labels
outside E. A label outside E that is pure among the remaining
targets is also pure in the original physical classes.
TwoTargetAllowedSingletonSelection proves the analogous
singleton dichotomy, using a finite fixed-degree sampling
lemma. It chooses either k distinct surviving mixed classes
with a common positive opposite degree and singleton degree
in one target, or two surviving actual pure classes per target.

TwoTargetWeakRegularization chooses the recovery parameter t
from s and the dimension-loss margin BEFORE C, theta and N.
For any actual weak aligned pair, choose any one supplied
bounded enlarged alignment a,b. The actual unit count is at
most theta*L+2. Removing all but at most one unit gives an
actual deletion D and its endpoint-label image E with
|E|<=2*theta*L+2, including the empty-unit case. The SAME
physical relation space P, recovery exclusion and coefficient
list are retained. For EACH target separately the surviving
label population is at least d-xi*L/4-(2*theta*L+2), and its
surviving singleton population is at least
2*d-xi*L/2-(L+1)-(2*theta*L+2). The latter subtracts |E| once,
rather than twice as in recomputing 2*m_remaining-(L+1).

TwoTargetOrientedClassPattern constructs one literal pattern
from the actual label classes and exposes its exact left and
right selected grids, pool membership, mixed and degree-one
validity and integer square roots in both orientations.
TwoTargetSelectedClassData combines it with the common
source-only coefficient list and proved finite-Runge selected
grid admissibility. Every selected nonzero label outside the
actual endpoint-label image yields actual bounded-size classes
avoiding all deleted endpoints. Their coefficients are
positive, at most N^(2*(t-1)), and drawn from one subpower list.
No chosen equation, grid, coefficient or host bound is an
additional arithmetic hypothesis.

TwoTargetWeakMixedCount and TwoTargetWeakSingletonCount apply
the existing chosen-source and ordinary geometric host counts
to those actual patterns. Their sole unproved properties remain
the inventoried source-surface cover, ordinary-surface cover
and normalized-curve count, at explicitly displayed finite
parameters fixed before N. The selected equations and their
admissibility are constructed internally. The mixed branch is
N^(1/2+epsilon); a fixed singleton orientation is N^epsilon.

TwoTargetWeakDenseCount uses xi=eta and intersection at most
eta*L/64. Positive effective relation rank d>=eta*L supplies
enough surviving target labels, hence the safe mixed/pure
alternatives and the complete half-power count. The pure
alternative uses the previously proved unconditional two-
equation count in each target. TwoTargetWeakUpperCount uses
xi=delta and intersection at most delta*L/64. When
 d>=(1/2+delta)*L the surviving singleton budget forces a
safe fixed-degree singleton orientation or the pure case,
giving the complete N^epsilon upper-stratum count.

TwoTargetWeakRankWeight chooses the positive theta as the
minimum of the two fixed intersection thresholds, and combines
the actual two rank strata with the full factor2^d. The actual
effective kernel has dimension at most L, including irregular
source and target windows. TwoTargetWeakMass multiplies by
the exact actual marginals and uses the uniform marginal cap
to prove mass<=N^(-1+epsilon). TwoTargetDenseMass partitions any
actual host population into its nonaligned and remaining weak
aligned parts and absorbs the finite sum into the margin.

TwoTargetAdmissibleDensePairs defines the literal full dense
population, including distinctness and all source exclusions,
and proves that every direct target pair satisfies its pair
condition. TwoTargetDensePairTheorem.article_15_2_dense_pair
then states the complete first displayed bound of15.2 with
the PRINTED deficit, using its proved equality with the actual
effective relation-kernel dimension. It is stronger than the
printed big-O bound because the constant is absorbed after a
common threshold. The primitive source-restricted displayed
bound still needs the exact family decomposition and source
marginal summation. No numbered completion is claimed yet.

No new external literature property, kernel axiom, dependency
download, Paper C port or source-manuscript edit is introduced.
Palomar remains deferred until full coverage and verification.

Verified under Lean v4.36.0-rc2: full build passed (13111 jobs); direct axiom audit passed for 9866 declarations using only propext, Classical.choice and Quot.sound; all 8093 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 13.85 GiB.


## Conditional completion of both conclusions of article15.2

Article Lemma15.2 is now COMPLETE CONDITIONALLY, including
BOTH of its literal displayed conclusions. The previous
checkpoint proved the full nonaligned-or-weak-aligned pair
mass, with source exclusion and the printed effective deficit.
The new SourceRestrictedDenseMass.article_15_2_source_restricted
proves the source-restricted dense homogeneous mass for actual
unordered primitive families of every fixed size r>=3.
Main15.2 moves from in_progress to conditional. Exactly the
three previously inventoried geometric properties remain
unproved; there is no additional source-restricted host-count
input. Unconditional numbered coverage stays82/167, while
conditional numbered coverage rises from14 to15. Confirmed
mathematical improvements remain124.

TwoTargetPrimitiveCut proves the exact generic algebra behind
the primitive consequence. Zero nullity on a disjoint union
forces its two actual effective spans to be direct. For a
nonempty source family E and two distinct targets outside E,
zero nullity of every proper subfamily gives directness of
each target from the complete source span and directness of
the two targets. The source family itself is direct. Its rank
sum therefore equals its effective span rank, and the full
relative nullity is exactly the two-target dimension deficit.
These facts concern actual effective spaces and remain valid
with local relations in the individual windows.

TwoTargetFamilyCover constructs the actual family obtained by
inserting two distinct targets outside E, and the actual finite
pair population whose resulting family belongs to F. Every
I containing E with |I|=|E|+2 is such an actual extension. A
proved nonnegative weighted cover bounds the sum over actual
unordered families by the sum over their prescribed source
collection and actual target pairs. It allows multiple source
representations and both target orders without any equality
or undercounting claim. No combinatorial cover is assumed.

TwoTargetPrimitiveData instantiates the generic primitive cut
for actual square-class spaces. It identifies the span of the
source set exactly with the indexed span of its injective
finite enumeration. For every actual primitive extension, the
full nullity equals the actual effective Kernel dimension;
its two targets are direct and hence satisfy the proved dense
pair condition for every nonnegative intersection threshold.
The heterogeneous homogeneous weight factors EXACTLY into
the actual source marginal product times p_y*p_z*2^d. The
source marginal product is bounded by the corresponding fixed
power of the uniform marginal cap.

TwoTargetPrimitiveExtensions applies the already proved full
dense-pair mass to each actual source set E of fixed positive
size s, before summing sources. Its geometric parameters and
common N0 precede all E, all actual primitive extension
populations F and every choice of targets. The direct target
pair condition is proved internally from primitiveness. With
M(C)=2*2^C it bounds the complete actual extension weight by
(M(C)/N)^s*N^(-1+epsilon). All factors are exact heterogeneous
marginals, and all arithmetic assumptions needed by the
conditional geometric bounds have already been proved.

SourceRestrictedDenseMass.article_15_2_source_restricted now
sums these actual extensions. The prescribed source collection
has actual sets of size r-2 in the dyadic block and cardinality
at most N^(a+epsilon/4). Each actual family in F lies in that
block, has size r, is primitive, has relative nullity at least
eta*L, and contains a member of that prescribed collection.
The proved finite weighted cover and source caps give mass at
most M(C)^(r-2)*N^(-(r-1)+a+epsilon/2). The fixed constant is
absorbed after one common threshold, yielding the literal
N^(-(r-1)+a+epsilon) conclusion. The source-count epsilon/4
makes explicit the companion's instruction to divide the final
exponent margin between the source count and conditional
estimate. It expresses the usual arbitrarily-small-margin
source-count hypothesis without spending the final margin
twice. The theorem uses the actual PrimitiveWindowMass.mass,
which is the printed sum of (product p_i)*2^rho(I).

The existing source-surface cover, ordinary-surface cover and
normalized-curve properties remain ordinary explicit theorem
arguments at fixed displayed finite parameters. Their imported
arithmetic preparation is proved; their geometric literature
translation is still open. Accordingly this completion is
conditional, not an unconditional proof or Palomar record.
There is no new literature property, mathematical finding,
axiom, dependency download, Paper C port or manuscript-source
edit. The original V1.6 sources remain byte-for-byte preserved.

Verified under Lean v4.36.0-rc2: full build passed (13121 jobs); direct axiom audit passed for 9881 declarations using only propext, Classical.choice and Quot.sound; all 8111 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 13.82 GiB.


## Unconditional completion of article15.3

Article Lemma15.3 is now proved UNCONDITIONALLY, for the actual
compressed-center population of every fixed positive channel
0<a<=b. DenseCompressedTargetCount.article_15_3 includes ALL
actual unit-offset patterns and the exact effective prescribed
space W. Coprimality, strict channel ordering, private primes,
local regularity and injectivity of the compressed selection
map are not needed for this stronger count. Main15.3 moves
from not_started to proved. Unconditional numbered coverage
rises from82 to83/167; the15 conditional results stay separate.
P1-MATH-0125 records the two-whole-class proof at logarithmic
width, bringing confirmed mathematical improvements to125.

LogarithmicSourceCoefficientCount proves the common source-
only coefficient pool bound with only an upper logarithmic
width for the actual source coordinate set and the prime
cutoff. Actual source values have the explicit height bound
N^2. The threshold precedes every source-value list, length
and cutoff. LogarithmicCoefficientPatterns proves the bounded
offset and common-list pattern count under the same upper
width alone. LogarithmicUnivariateCount then applies the
proved unconditional two-disjoint-square-equation estimate on
any fixed comparable positive interval. Its integer coefficients
need only be nonzero and come from a common subpower list;
no coefficient height or unformalized curve estimate is used.

IntersectionKernelLift embeds W intersect S_y in the actual
two-target relation kernel by (u,-u,0). Its auxiliary target
projection is identically zero and its first target projection
is injective. OneTargetPhysicalLift composes this with the
proved arbitrary effective sections, obtaining an injective
physical lift of the ACTUAL intersection. Sources may overlap,
be dependent or have local relations.

OneTargetPhysicalRegularization chooses t from the source
number and rank margin before all actual windows and W. It
regularizes the pulled-back physical coordinate forms and
pushes the shared subspace into the literal physical code.
The image has intrinsic recovery exclusion, retains rank at
least dim(W intersect S_y)-xi*L/4, has injective first target
projection and still has identically zero auxiliary target.
The first target separately has at least dim(P) distinct
nonzero coordinate labels. Every nonzero class has no
coordinate at all in the auxiliary target.

OneTargetClassSystem consequently chooses just TWO distinct
actual target labels. Their physical classes have uniformly
bounded size, disjoint nonempty target offsets and coefficients
in the common full squarefree source-only list. The actual
square roots and both univariate square equations are proved.
OneTargetLogDenseCount combines these constructions with the
logarithmic pool and two-equation counts. It gives N^epsilon
actual dense targets on every fixed comparable positive interval,
for ANY sufficiently large logarithmic length, above ANY
prescribed subspace of the actual source span. The threshold
precedes every source, W, target population and actual code.
The old strict-product-certificate/residual-prime-group
classification is not required for this alternative proof.

BoundedWidthWindows embeds every actual finite set in
X+[-R,R] into the complete original window starting at
X-R+1 with length2R. It proves monotonicity of the actual even
square-class spaces and injectivity of this shifted center
once X>=R. BoundedWidthDenseCount uses this embedding with
R=D*(L+1). The enlarged length remains logarithmic; all old
source windows embed in the corresponding longer source
windows. Their actual values satisfy the fixed height bound
uniformly. A fixed reduced density margin retains the original
intersection threshold eta*L. The shifted center stays in a
fixed comparable positive interval. Thus the count applies to
EVERY actual family U_X of bounded width, even when it varies
with X and has local square relations. No injectivity of its
even-selection map is assumed.

CompressedTargetCenters constructs the actual centers as the
image of actual dyadic source pairs with an exact unit at the
chosen two offsets. Its block is exactly the previously proved
compressed union of the two normalized windows. Its width is
at most b*(L+1), with center between N/2 and3*b*N. The literal
dense population filters the actual effective intersection
with W. Every actual compressed pair satisfying that rank
condition is proved to belong to the population, and all unit
offset patterns are included in allDenseCenters.

DenseCompressedTargetCount first applies the general bounded-
width count uniformly to every offset pair. It then sums all
(L+1)^2 choices, absorbing this factor into the exponent margin.
The final article_15_3 theorem counts the actual compressed
centers, with one N0 before the critical length, every source
tuple, every W and all offset patterns. It proves card<=N^epsilon,
which implies the printed big-O conclusion. A fixed finite
set of channels can be summed with the same margin convention.
This proof uses only established unconditional arithmetic,
linear algebra and two-equation estimates.

There is no new external literature property, kernel axiom,
dependency download, Paper C port or manuscript-source edit.
The broader project remains incomplete and Palomar is deferred.

Verified under Lean v4.36.0-rc2: full build passed (13145 jobs); direct axiom audit passed for 9906 declarations using only propext, Classical.choice and Quot.sound; all 8141 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 13.77 GiB.


## Conditional completion of article15.7

Article Lemma15.7 is now complete CONDITIONALLY on exactly the
three already recorded geometric properties used for article11.1:
chosen-source surface covers, ordinary surface covers and uniform
normalized-curve point bounds. No additional analytic premise or
desired extension bound is assumed. Main15.7 moves from not_started
to conditional. Unconditional coverage remains83/167; conditional
coverage rises from15 to16, separately. P1-MATH-0126 records a
minimal-relative-seed simplification of the proof. All original
manuscript bytes are preserved and Palomar remains deferred.

ErasedNullityRelations proves that a positive actual relation
space, whose erasures vanish at designated target indices, has
one actual relation nonzero at every designated target. Other
reserved components are allowed to vanish. MinimalRelativeRelations
adds one actual source span as an Option-indexed block, proves
the exact relative dimension identity, identifies zero nullity
with the existing compressed directness predicate, and extracts
a minimal nonempty target subset and its full-target-support
relative relation. The source component may be zero. This handles
both internal target dependence and dependence on the old source
span with the same actual construction.

RelativeWindowFamilies defines actual unordered target families
with a nonzero participating vector at each target, above the
prescribed source space. It proves coverage by injective actual
enumerations in the existing conditional half-count population.
RelativeOriginalWindowMass proves, unconditionally and uniformly,
count at most N^(h/2+delta) and independent heterogeneous mass at
most N^(-h/2+delta), for any fixed h and any prescribed space
inside the sum of a fixed number of actual old dyadic windows.
The one threshold precedes N,L,all source centers,the prescribed
space and the actual target ground set. All exact marginals,
including zero marginals, remain unchanged.

FixedPairExtensions defines precisely the actual U disjoint from
the pair e, of cardinality k, for which the compressed source
space and the individual new spaces fail directness. Its proved
membership equivalence uses the existing literal compressed-block
directness predicate. Every such U contains a minimal relative
seed of some size1<=h<=k. Actual finite weighted coverage and the
seed product estimate bound all remaining independent factors by
(M+1)^k when the total actual marginal mean is at most M. At h=1,
the seed mass is exactly the marginal sum over targets meeting
the pair span. Summing over ALL dyadic pairs gives precisely the
previous IndependentTargetDeficit: pair activity vanishes for
direct pairs. No positivity restriction on the actual activity
or Bernoulli marginals is introduced.

The exact finite bound is
D_k <= (M+1)^k * (D_1 + k*Q*A_2),
where Q uniformly bounds every seed mass of size2 through k,
D_1 is the literal unary deficit and A_2 is the full actual
absolute pair activity. The actual mean bound gives M=2*2^C.
With delta=epsilon/8 the proved relative half-count gives
Q=N^(-1+delta); article11.1 gives D_1<=N^(-3/2+delta)
and A_2<=N^(-2/3+delta). The higher-seed contribution is
therefore at most N^(-5/3+2*delta), and the finite k-dependent
constant is absorbed into the exponent margin.

FixedPairExtensionDeficitUnderInputs.article_15_7 proves the
literal final N^(-3/2+epsilon) bound. The finite geometric caps
are chosen before the corresponding geometric arguments, then
the common threshold precedes every actual N,L and G subset of
the dyadic block. The threshold may depend on fixed k,C,epsilon;
no growing-order or all-cardinality conclusion is asserted.
The geometric properties themselves remain unformalized inputs.
No new dependency, PaperC port or registration is added.

Verified under Lean v4.36.0-rc2: full build passed (13157 jobs); direct axiom audit passed for 9931 declarations using only propext, Classical.choice and Quot.sound; all 8176 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 13.74 GiB.


## Original-window all-cardinality independent tail

The ORIGINAL-WINDOW assertion of article Lemma15.8 is now proved
UNCONDITIONALLY at all cardinalities. For every fixed v>0,a<2 and
epsilon>0, one fixed cutoff s and one threshold precede all N,L
and all actual dyadic ground sets. The literal sum over actual
full-support families of cardinality at least s, weighted by
the exact product of v*p_x, is at most N^(-a+epsilon). Overlapping
windows, local relations, incompatible affine systems and zero
marginals are all retained. The separate assertion with one fixed
compressed block is NOT yet proved. Main15.8 moves to in_progress;
unconditional coverage stays83/167 and conditional coverage16.
P1-MATH-0127 records the stronger participating-family bridge.

ParticipatingWindowCertificates lifts actual effective relations
to actual even physical window words. A selected large odd prime
has an actual receiving value with ODD valuation in another
window, not just a divisibility witness. Every unmarked window
that participates in some actual relation yields either an actual
moderate certificate for the entire tuple or an actual outgoing
saturation edge. The proof is uniform in the finite order; no
bound on the number of windows or growing-order constant is used.
The existing moderate and saturation estimates are then applied
to their exact original arithmetic populations.

AllFamilyEnumerations injects every actual unordered family
together with ALL permutations of its enumeration into the
actual tuple population. It proves F.card*r!<=tuplePopulation.card.
WindowCertificateFamilies uses a universal enumeration predicate
for certified families and proves that a family failing this
predicate has an actual enumeration with no moderate certificate.
The coordinate alternative makes its literal subtype vertex set
admissible in the actual marked saturation graph. Exact vertex
images and cardinalities are proved. WindowCertificateMass uses
the factorial divisor at every order and then sums the actual
finite family layers against the already proved summable moderate
certificate series. The factorial never estimates the growth
of an arithmetic constant depending on the order.

MarkedWindowCount proves the actual marked-center count
N^[1-(1-beta)*(1-sigma)+epsilon] for Y=log(N)^A,T=N^beta,
provided sigma>=1/2,sigma<1,A*(1-sigma)<1. It starts from an
actual B-position cover of marked centers and the proved Rankin
bound. Upper logarithmic width alone suffices for this count.
PowerTiltedGraphTail applies the actual marked-star generator.
UniformGraphCardinalityTail has ONE threshold before every
cardinality cutoff s and every finite graph: if its vertex count
is at most N and both mark count and maximum degree are at most
N^(1-2*theta), its independent tail with weight at most M/N is
at most N^(-theta*s+epsilon). Tilting by N^theta leaves the full
generating function bounded by exp(M+8*M^2).

OriginalParticipatingTail splits an actual finite population by
its certificate predicate and proves its mass is at most
N^(-2*beta+4/A+epsilon)+N^(-theta*s+epsilon). Its threshold precedes
all orders, every nonnegative heterogeneous weight function
bounded by M/N, and every actual family population in the dyadic
block. Crucially it needs only that EACH target participates in
SOME relation; a single relation using all targets is unnecessary.
Explicit parameter choices prove the subcritical a<2 tail with
s fixed before N. FullSupportIndependentTail.article_15_8_original
specializes this stronger statement to the literal actual
full-support population and the true Bernoulli marginals.

No geometric input, desired target estimate, dependency download,
PaperC port, manuscript-byte change or Palomar registration is
added. Compressed blocks, the all-cardinality pair deficit and
positive or centered masses amplified by relative nullity remain
separate open tasks.

Verified under Lean v4.36.0-rc2: full build passed (13177 jobs); direct axiom audit passed for 9958 declarations using only propext, Classical.choice and Quot.sound; all 8209 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 13.69 GiB.


## Unconditional completion of companion T22.1

Companion Proposition T22.1 is now proved UNCONDITIONALLY,
including the literal ordered-list sum with weights u^r/r!
and nominal factor p^r, p=2^(-L). The actual manuscript list
population requires distinct dyadic starts, full effective
support, rank L at every window, and pairwise distance greater
than L. FullSupportOrderedLists.mem_manuscriptLists identifies
all these actual conditions. No minimality or affine
compatibility is imposed. The printed bound is exactly
N^(-2*s/(2*s+1)+epsilon) for each fixed s>=2.
T22.1 moves from not_started to proved. Unconditional numbered
coverage rises from83 to84/167; the16 conditional results stay
separate. P1-MATH-0128 records a stronger N^(-1+epsilon) bound.

FamilyEnumerationUpper proves the reverse factorial inequality
by injecting actual ordered tuples into their actual finite
family and the permutation of its canonical enumeration.
Together with the previously proved forward injection it gives
the exact identity #lists=r!*#unorderedFamilies. It includes
empty and singleton orders as well. FullSupportOrderedLists
proves the exact cardinality identity for the real full-support
tuple population, cancels the actual factorial, and identifies
the sum over all orders with the actual unordered family sum.
The nominal-weight formula is exactly the expression printed
in T22.1. The manuscript population is a proved subset of this
larger actual list population, so its weighted count follows
without a counting assumption.

OriginalParticipatingMass.fixed_mass proves independent mass
at most N^(-r/2+epsilon) at each fixed order r, for arbitrary
nonnegative heterogeneous weights bounded by M/N and actual
coordinatewise participating families. It uses the proved
relative half-count with no old sources, and the actual family
inclusion, not a supplied desired host estimate.
OriginalParticipatingMass.uniform_mass combines these finitely
many fixed-order bounds with OriginalParticipatingTail's uniform
all-cardinality tail. The small-order cutoff is chosen before N;
only the finitely many orders below that cutoff use their own
fixed-order thresholds. The large orders use the already proved
uniform certificate generator. The total mass of ALL such
families of size at least two is at most N^(-1+epsilon).
The threshold precedes every actual weight function and family
population; zero weights and all actual overlaps are allowed.

FullSupportWeightedCount.uniform_ordered_mass specializes to
the nominal constant weight u*2^(-L), whose cap is proved from
the critical-band condition. It gives N^(-1+epsilon) for the
larger actual injective full-support list population, without
regularity or separation, with one threshold before EVERY
cutoff s>=2. The stated source exponent follows because
2*s/(2*s+1)<=1. FullSupportWeightedCount.companion_T22_1 then
restricts to the literal separated regular manuscript lists.

The strengthening concerns INDEPENDENT product weights. It
does not establish positive joint or centered masses containing
the factor2^rho, nor the separate compressed-block assertion of
main15.8. No geometric input, dependency download, PaperC port,
original manuscript edit or Palomar registration is added.

Verified under Lean v4.36.0-rc2: full build passed (13185 jobs); direct axiom audit passed for 9974 declarations using only propext, Classical.choice and Quot.sound; all 8229 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 13.67 GiB.


## Uniform first moment of the actual rough-prime window product

Preparation of the all-cardinality independent deficit15.6:
the rough-prime WINDOW AVERAGE in its proof is now established
unconditionally, with an explicit constant and without treating
the number of exposed sources as fixed. Main15.6 moves from
not_started to in_progress. Its final deficit estimate is NOT
yet proved. Coverage remains84/167 proved and16 conditional,
with128 confirmed mathematical improvements. This checkpoint
adds arithmetic foundations and no new numbered completion.

FiniteEulerAverage proves the exact finite divisor expansion
of an arbitrary nonnegative local Euler product over a finite
set of distinct primes. For every natural X, the average over
1<=n<=X is at most
X*product_p(1+h(p)/p).
The exact expansion uses the actual count floor(X/d) of positive
multiples of the product d of the selected distinct primes.
Primality supplies the actual coprimality implication d|n iff
every selected prime divides n. In particular there is no
spurious +1 term for each modulus in this first-moment bound.

InverseSqrtTail proves the finite elementary bound
sum_{Y<n<=X} n^(-3/2) <= 2/sqrt(Y), for every Y>=1.
It telescopes reciprocal square roots and does not invoke an
analytic tail premise or any prime-distribution estimate.
RoughEulerMoments uses the cutoff Y=64*B^2 and the actual
factor p^(-1/2). For p>Y the moment increment
h_B(p)=(1+p^(-1/2))^B-1 is at most8*B*p^(-1/2).
The already proved elementary exponential remainder gives
this bound since B/sqrt(p)<1/8. The finite tail bound gives
sum_p h_B(p)/p<=2 for EVERY finite prime set above this cutoff.
Consequently the actual B-th moment of the local rough-prime
Euler product, summed over1<=n<=X, is at most X*exp(2),
uniformly in B and in the actual finite prime set.

FiniteProductPowerMean proves the pointwise AM-GM inequality
product_i f_i <= average_i f_i^B for B positive positions,
and the finite first-moment consequence after interchanging
the actual sums. This suffices in place of the printed Holder
step. WindowEulerAverage.first_moment applies it to every true
position x-1+i of an actual complete dyadic window. Each fixed
position maps the actual starts injectively into1..3N.
For N>=2 and1<=B<=N+1 it proves
sum_{N<=x<2N} product_{i<B} product_{p in P,p|(x-1+i)}
  (1+p^(-1/2)) <= 3*N*exp(2),
for EVERY finite prime set P above64*B^2. This product counts
a prime once for every position it divides and therefore also
majorizes the single-occurrence union-of-primes product in
the manuscript. The explicit bound is independent of B.

The constant enlargement from the printed cutoff B^2 to64*B^2
is internal to these new lemmas; no preserved manuscript is
changed. The old-source Euler factor, the actual relative
exceptional exposure count and its entire cardinality sum
remain to be connected before15.6 can be completed. No desired
deficit bound or growing-order arithmetic constant is assumed.
There is no new geometric or literature input, PaperC port,
dependency download, original-source edit or Palomar registration.

Verified under Lean v4.36.0-rc2: full build passed (13195 jobs); direct axiom audit passed for 9990 declarations using only propext, Classical.choice and Quot.sound; all 8249 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 13.65 GiB.


## Uniform actual independent-exposure rows

The ARITHMETIC exposure budget for article15.6 is now proved
unconditionally with a threshold before every number of preceding
windows. Its final independent deficit sum is still OPEN.
Main15.6 remains in_progress; coverage remains84/167 proved,
16 conditional and128 confirmed mathematical improvements.

LogBudgetEuler proves the finite prime Euler-product estimate
exp(c*sqrt(Y)/log(Y)+K/(sqrt(Y)*log(Y))) from the ACTUAL prime
logarithmic budget sum(log(p))<=K. Small primes are bounded by
the proved elementary weighted-prime estimate; above Y each
inverse square root is charged to log(p)/(sqrt(Y)*log(Y)).
No prime-pool cardinality estimate is substituted for its log
budget. EulerPrimeCovers proves the monotonicity and finite
union-cover bounds, allowing repeated prime occurrences and
arbitrary overlaps.

IndependentExposurePrimePool defines the literal old-source
pool together with ALL primes up to Y=64*(L+1)^2. Its Euler
factor baseEuler(S,L) is at most N^epsilon uniformly for every
actual dyadic source set S with card(S)<=s, where s is fixed
before N. The actual log budget is
Y*log(4)+B*log(4)+s*B*log(3N), B=L+1.
Since sqrt(Y)=8B, the exponent is at most
[8*(c+log(4))*B+log(4)/8+s*log(3N)/8]/log(Y).
Critical-window geometry puts B<=D*log(N), and a fixed minimum
length makes log(Y) arbitrarily large before any actual source
is supplied. Thus this factor is uniformly subpower. All primes
of the real source values are retained.

IndependentExposureEulerBudget defines the actual rough-prime
window product A_x, with primes bounded by3N and above Y.
It has A_x>=1 and the already proved first moment at most
3*N*exp(2). For any fixed old source set S and ANY new set A
of dyadic windows, with NO bound on card(A), it proves
Euler(primePool(rawValues(S union A)))
  <= baseEuler(S,L)*product_{x in A} A_x.
The literal prime-set cover follows from actual prime factors
of actual true window values. A prime at most Y goes into the
base pool; every larger prime from a new window occurs in its
actual positionwise rough-prime Euler product.

For arbitrary weights w_x<=M/N, M>=0, the same development
proves sum_x w_x*A_x<=3*M*exp(2). The exact exceptional row is
BranchingExceptional.badStarts for all raw old source values.
Its weighted mass is at most
rowConstant(S,N,L,M)*product_{x in A} A_x,
where rowConstant=(M/N)*(B/2)*sqrt(3N)*baseEuler(S,L).
This uses the exact supported-value Euler count, including
contacts and local defects, with no separate contact deletion
or worst-case arithmetic constant depending on card(A).

UniformIndependentExposureBudget.uniform_row_constant proves
rowConstant<=N^(-1/2+epsilon), uniformly in fixed-cardinality
sources. uniform_budget therefore supplies ONE threshold
before all N,L,S,weights and arbitrarily large preceding sets A,
simultaneously with the constant weighted mean of A_x. These
are actual arithmetic row estimates, not assumptions of the
desired final independent deficit.

The remaining work for15.6 is finite: relate failure of the
literal source-plus-target directness to an exceptional exposure
in every ordering, retain the exact factorial enumeration, and
sum the weighted exposure bounds over all cardinalities. This
checkpoint asserts none of these unfinished closure steps.
No new external input, dependency download, PaperC port,
manuscript-byte change or Palomar registration is added.

Verified under Lean v4.36.0-rc2: full build passed (13205 jobs); direct axiom audit passed for 10010 declarations using only propext, Classical.choice and Quot.sound; all 8276 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 13.63 GiB.


## Unconditional completion of the uniform independent deficit

Main Lemma15.6 is now proved UNCONDITIONALLY for the literal
independent deficit summed over ALL cardinalities. One threshold
is chosen before N,L,all actual dyadic source and target sets,
every source set of cardinality at most the fixed s, and every
subspace W of the FULL RAW source value span. The result is
therefore stronger than restricting W to the effective source
span. The ground set G may be any actual subset of the dyadic
block; targets are exactly G minus the sources.

IndependentExtensionDeficit.Direct means literal injectivity of
the addition map from W and the individual effective spaces S_x.
Its equivalence with zero relative nullity is proved. The finite
population is exactly every target subset for which this map
is not injective, with no restriction on cardinality. Its weight
is exactly u^card(U)*product_{x in U} infiniteMarginal(x,L),
proved equal to product_{x in U}(u*infiniteMarginal(x,L)). Zero
marginals are retained. These are independent product weights,
not conditional extension probabilities or positive joint weights.

IntersectionExceptional proves that a nonzero vector belonging
both to an actual effective window space and to the full old
raw-value span forces at least two supported physical positions.
The even coefficient vector is lifted from the actual effective
space; its nonempty binary support has even cardinality. Every
selected coordinate lies in the real old prime pool by the
already proved private-prime argument. Thus its center belongs
to the literal BranchingExceptional.badStarts set. The effective
source span is proved to lie in the raw source-value span. The
latter has an actual finite enumeration from the full coefficient
map, so arbitrary source subspaces can be used without assuming
local regularity or a dimension formula for W.

For each non-direct U, choose a minimal relative dependent J
inside U. A genuine relation is nonzero in every target of J;
its sum lies in W. Choose x in J and put A=J minus x. The x
component is nonzero and lies in the full raw span of sources
union A. Hence x is an actual exceptional start relative to A,
and insert(x,A) is a subset of U. This covers internal target
dependence as well as dependence meeting W. The W component
may vanish, and no nonzero-source-component condition is added.

AllCardinalitySeedBound proves the exact finite identity for
all supersets of a seed D inside G:
  sum_{D subset U subset G} product_U w
    = product_D w * product_{G minus D}(1+w).
ExceptionalSeedBound then bounds every covered family by
  exp(sum_G w) * sum_{A subset G} product_A w * badRow(A).
If badRow(A)<=D*product_A a, a_x>=1, and
sum_G w_x*a_x<=K, this is at most D*exp(2K).
This is a pure finite unordered argument; no enumeration by
orders, factorial normalization or growing-order constants
are used in this closure. Overcounting is justified solely by
nonnegative finite sums, including overlaps between witnesses.

UniformIndependentDeficit.finite_bound applies this identity
to the actual source-relative seeds. The published arithmetic
row budget supplies D=N^(-1/2+eta), a_x=windowEuler(N,L,x),
and K=3*M*exp(2), where M=u*2*2^C is a uniform actual marginal
cap. These inputs hold before arbitrarily large preceding sets A.
The already proved first moment bounds K independently of N,L.
With eta=epsilon/2, the fixed factor exp(2K) is absorbed using
a second epsilon/2. UniformIndependentDeficit.uniform_bound
therefore proves the full printed N^(-1/2+epsilon) estimate,
uniformly in sources and W, at every cardinality simultaneously.
Contacts and local defects remain in the exceptional row; no
extra contact deletion or correction term is necessary.

Main15.6 moves from in_progress to proved. Numbered unconditional
coverage rises from84 to85/167;16 conditional results remain
separate. P1-MATH-0129 records the unordered finite closure and
the stronger raw-source-space scope. This result does not prove
the compressed clause of15.8 or the pair-weighted total15.9.
No new geometric input, dependency download, PaperC port,
manuscript-byte change or Palomar registration is introduced.

Verified under Lean v4.36.0-rc2: full build passed (13215 jobs); direct axiom audit passed for 10026 declarations using only propext, Classical.choice and Quot.sound; all 8298 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 13.60 GiB.


## Conditional completion of the pair deficit at every cardinality

Article Proposition15.9 is now complete CONDITIONALLY under
exactly the existing chosen-source surface covers, ordinary
surface covers, and uniform normalized-curve point bounds.
AllPairExtensionDeficit.deficit is the literal D_2(u): sum over
ALL unordered actual dyadic pairs of the absolute actual centered
coefficient times the exact independent extension deficit over
EVERY cardinality, with the actual heterogeneous marginals.
AllPairDeficitUnderInputs.article_15_9 proves its eventual bound
N^(-3/2+epsilon). No desired pair or extension mass is assumed.
Main15.9 moves from not_started to conditional; unconditional
coverage remains85/167, conditional results rise from16 to17,
and confirmed mathematical improvements rise from129 to130.

RelativeParticipatingUnion proves a stronger algebraic bridge
than a simultaneous full-support relation. If every source
coordinate participates in some relation, and every target
coordinate participates relative to the effective source span,
then EVERY coordinate in the original source-target union
participates in some relation with zero total. For a target,
its actual relative sum is lifted through the actual addition
map onto the source span, and subtracted after extension by zero.
For a source, its source-only relation is extended by zero.
Every actual dependent pair is participating, since it is a
minimal non-direct two-element family. Source coordinates may
vanish in target witnesses. No claim of a single relation
nonzero at all source-target coordinates is made or needed.

DistinguishedSeedWeights proves the exact finite overcounting
bound for a distinguished disjoint source e and target seed A.
If c(e)<=R*product_e(w), then
  sum_e c(e)*sum_A product_A(w)
    <= R*sum_I product_I(2*w),
provided each union I=e union A belongs to the target family.
For each fixed e, A is determined by I because e and A are
disjoint. For fixed I, at most2^card(I) choices of e exist.
That factor is absorbed exactly by doubling the independent
weight, before any cardinality cutoff or N is chosen.
PairExtensionSeedTail applies the bridge to actual relative
participating seeds disjoint from each dependent pair.

GoodPairSeedTail.private_product proves the exact product
of actual marginal weights for a private channel pair:
product_e(u*p_x)=u^2*(2^(-L))^2.
The existing actual covariance estimate divided by this product
is at most2^((L+1)/3)/u^2, since every channel in the finite
good family has height b>=3. In the critical band this is at
most K*N^(1/3), K=2^((C+1)/3)/u^2. uniform_ratio has one threshold
before every actual good pair in the fixed finite channel set.
The doubled weights2*u*p_x have a fixed cap4*u*2^C/N.
The already proved original coordinatewise-participating tail,
with a=23/12<2, bounds all unions of large relative seeds by
N^(-23/12+eta). Multiplying by the ratio gives
K*N^(-19/12+eta), stronger than the required N^(-3/2+epsilon).
This entire good-pair large-seed estimate is UNCONDITIONAL.
It uses original windows and does not use a compressed-block
certificate theorem or assume a compressed-tail estimate.

AllPairExtensionDeficit proves the remaining exact finite cover.
Every failed extension contains a minimal nonempty relative seed.
Seeds of size below fixed s are covered by the actual fixed-order
extension populations of15.7; all larger ones belong to the
actual relative participating-seed tail. The exact finite
superset identity charges free complements by exp(sum_x u*p_x).
After weighting pairs, each fixed small seed order contributes
u^k*FixedPairExtensions.deficit(G,L,k). The cutoff s is chosen
before N, so only finitely many fixed-order bounds are used.
The class partition is an equality for the literal weighted
D_2, including all direct pairs with their zero coefficients.

UniformPairClassDeficit proves that ANY actual pair class has
mass at most its absolute activity times N^(-1/2+eta), using
unconditional15.6 with the actual full raw source span. The
proved finite-channel weak and exceptional activity bounds,
N^(-1+eta) and N^(-1+eta), therefore yield N^(-3/2+O(eta)).
The good-pair small seeds use the existing conditional15.7,
and their large seeds use the new unconditional estimate.
The true actual marginal mean bounds the free-complement
factor by exp(u*2*2^C). All finite factors are absorbed after
choosing eta=epsilon/16.

FinitePairDeficitInputs.Parameters and Hypotheses are only a
finite explicit bundle of the SAME geometric propositions.
They contain no host estimate, arithmetic mass bound or new
axiom. The final theorem chooses Q,s and finitely many actual
geometric dimensions before their supplied hypotheses, then
one threshold before all N and critical L. The chosen-source
size caps are sizeCap(epsilon/2048) for the pair partition and
sizeCap(epsilon/65536) for each of the finitely many fixed seed
orders. The three geometric translations themselves remain
unformalized, so this result is NOT counted as unconditional.

P1-MATH-0130 records that the stronger coordinatewise-tail
property removes the geometric-compression step from the proof
of15.9, and also removes the need to separate internal target
dependence in this argument. Main15.8's separate compressed
assertion remains OPEN; this checkpoint does not claim it.
No new dependency, PaperC port, original-source change or
Palomar registration is introduced.

Verified under Lean v4.36.0-rc2: full build passed (13231 jobs); direct axiom audit passed for 10049 declarations using only propext, Classical.choice and Quot.sound; all 8328 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 13.56 GiB.


## Unconditional completion of companion T17.1

Companion Lemma T17.1 is now complete UNCONDITIONALLY, with
stronger independent deficit powers than the printed statement:
  F <= N^(-1+epsilon),
  mathfrakG <= N^(-7/6+epsilon).
These are the literal two retained-reference counting deficits,
including their original2^r cardinality weights, actual nominal
marginal on the regular ground, and actual good-pair joint
probabilities. RetainedIndependentDeficitRates.companion_T17_1
proves exactly the printed weaker rates
F<=N^(-4/5+epsilon)+(L+1)/N and mathfrakG<=N^(-1+epsilon).
The existing exact cardinality grouping identifies the complete
sums over0<=r<=n; coefficients above n are already zero.
The common threshold precedes every critical L and EVERY real
private-prime threshold H, including a scale-dependent H.

OrdinaryIndependentDeficit defines ALL non-direct subsets of
an actual original-window ground set with arbitrary independent
product weights. Each contains an ordinary primitive subset.
Every primitive subset has size at least two and is genuinely
coordinatewise participating; its simultaneous full-support
relation is also proved. The exact finite superset cover gives
mass<=exp(sum_G w)*primitiveSeedMass. The already proved
OriginalParticipatingMass.uniform_mass bounds every such seed
population by N^(-1+eta), for arbitrary heterogeneous w>=0
with w_x<=M/N. The total weight is at most M, since the dyadic
block has exactly N starts. After absorbing exp(M),
OrdinaryIndependentDeficitBound.uniform_bound proves the entire
non-direct independent mass<=N^(-1+epsilon), uniformly over
all actual dyadic ground sets and all weights with the fixed cap.
No positive joint mass or relative-nullity amplification is
substituted for these independent product weights.

RetainedIndependentDeficitComparison.first_eq identifies the
literal firstMass with that development at w_x=2*p_x on the
actual regular set. failed_eq identifies the actual failed
compressed extensions with literal non-directness of the source
span plus individual target spaces. second_eq proves the exact
identity
  secondMass(H,N,L)=4*sum_good_e q(e)*E_{S_e}(2),
with all cardinalities present. The factor4 is exactly the two
original endpoints' cardinality weight, not an asymptotic loss.
These identities use effective spaces and do not assume direct
factorization of any failed dependent extension.

Every prime is positive, so an actual PrivateAbove(H) condition
implies PrivateAbove(0), even for arbitrary real H. Actual good
edges lie in the two private channel families2:3 and3:4 at
cutoff0; the at-least-two-unit property follows from actual
nonzero intersection and private normalized values. Their true
joint mass is bounded by the actual homogeneous rank probability,
then by the previously proved raw principal homogeneous mass.
RetainedGoodPairMass proves beta(H,N,L)<=N^(-2/3+eta), uniformly
in ALL H, with no H-range assumption and no new geometry.
This is an upper bound; it asserts no uniform lower phase at
arbitrary H.

Uniform independent deficit15.6, with exactly two old sources
and u=2, gives E_{S_e}(2)<=N^(-1/2+eta) for every good pair,
including all its failed extensions and exact zero marginals.
The exact secondMass identity thus gives
4*beta*N^(-1/2+eta)<=N^(-7/6+epsilon).
The actual marginal cap supplies the firstMass specialization
with M=4*2^C. Both stronger estimates are unconditional.
Consequently T17.1 needs neither the positive primitive
mass theorem nor the distinguished compressed positive-mass
theorem used in its printed proof. No conclusion about those
separate positive-mass theorems is inferred.

T17.1 moves from not_started to proved; unconditional coverage
rises from85 to86/167;17 conditional results remain separate.
P1-MATH-0131 records the stronger powers and simpler independent
proof. All geometric translations remain explicit unproved
arguments in their separate conditional results. No new
external input, dependency download, PaperC port, manuscript
byte change or Palomar registration is introduced.

Verified under Lean v4.36.0-rc2: full build passed (13241 jobs); direct axiom audit passed for 10065 declarations using only propext, Classical.choice and Quot.sound; all 8347 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 13.54 GiB.


## Conditional completion of companion T17.4

Companion Lemma T17.4 is now complete CONDITIONALLY under
the same three already recorded finite geometric properties:
chosen-source and ordinary surface covers, and uniform actual
normalized-curve counts. Its entire finite analytic inequality
remains unconditional. The only use of geometry in this
completion is the arithmetic upper bound for the ACTUAL
regular-set covariance parameter at the literal a_N scale.
No desired conversion error or covariance bound is an input.

SecondFactorialCorrection.value is exactly
a_N=E(Z_N)_2-(N*2^(-L))^2, for the full actual dyadic count.
The second factorial moment is the actual Bochner expectation,
not an independent approximation. gap_identity proves
a_N-kappa_2=(E Z_N)^2-lambda_N^2, with the full diagonal
correction retained. The previously proved actual mean-bias
estimate and actual mean caps give, unconditionally,
|a_N-kappa_2|<=N^(-1+epsilon).

SecondFactorialCorrectionLower.uniform_lower proves the
unconditional lower bound a_N>=c_C*L*N^(-2/3), c_C>0.
The actual positive2:3 channel gives a lower bound for beta;
the already proved one-sided full-cumulant comparison gives
2*beta-kappa_2<=N^(-1+epsilon). Together with the actual
mean-square gap this yields the claimed lower bound after
absorbing two N^(-11/12) errors. Thus positivity of the
literal a_N does not rely on the conditional upper profile.
This extends the already recorded unconditional positivity
argument of finding87 to the literal nominal correction.

SharpCovarianceScaleUnderInputs.uniform_absolute_scale
uses the existing actual pair-activity profile with fixed
margin1/15 and the unconditional principal beta upper phase.
The profile remainder N^(-4/5+1/15)=N^(-11/15) is smaller than
L*N^(-2/3). It proves the sharp bound
absolutePairMass(G,L)<=K_C*L*N^(-2/3) for EVERY actual
dyadic subset G, with NO epsilon in this power. The actual
regular covariance sum C_2 is bounded by this absolute mass.
Using the unconditional lower bound for a_N gives
|C_2|<=R_C*a_N. Both the signed covariance definition and
all possibly incompatible pairs remain exact.

SecondFactorialCorrection.regular_mean proves that the
actual regular-set count mean is n*p, n=card(G_N), p=2^(-L).
regular_cumulant proves its actual second factorial cumulant
equals2*C_2-n*p^2. The existing CountVariance identity
identifies that parameter exactly with variance minus mean.
There is no omitted marginal diagonal or change of mean.

SharpRetainedConversionUnderInputs.companion_T17_4 inserts
these actual parameters into the previously proved full
signed-measure conversion. It gives the literal ordinary l1
sum of absolute singleton errors over ALL k>=0:
  ||B_beta-Q(mu,alpha_G)||_1
    <=4*|beta_N-C_2|+K_C*(N^(-2)+a_N/N).
Here B_beta is the actual finite binomial pair reference
embedded as a signed measure, beta_N is the actual joint
mass of retained good edges, C_2 is the actual regular
covariance sum, mu is the actual regular mean, and alpha_G
is its actual variance-minus-mean parameter. Every real
private-prime threshold H is allowed; the beta discrepancy
is kept explicit, so no approximation beta_N=C_2 is assumed.
The exact coefficient4 is retained.

The geometric dimensions are chosen before their explicit
Hypotheses bundle, with chosen-source sizeCap(1/100).
After those supplied properties there is a constant K_C
and one threshold before every N,L and H. Those three
geometric translations themselves remain unformalized;
T17.4 moves from in_progress to conditional, not proved.
Unconditional coverage remains86/167; conditional results
rise from17 to18;131 confirmed improvements remain unchanged.
No new literature input, dependency download, PaperC port,
manuscript-byte edit or Palomar registration is introduced.

Verified under Lean v4.36.0-rc2: full build passed (13249 jobs); direct axiom audit passed for 10073 declarations using only propext, Classical.choice and Quot.sound; all 8357 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 13.51 GiB.


## Conditional completion of fixed and all-cardinality primitive mass

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

Verified under Lean v4.36.0-rc2: full build passed (13265 jobs); direct axiom audit passed for 10094 declarations using only propext, Classical.choice and Quot.sound; all 8385 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 13.47 GiB.


## All-order moderate certificates with a fixed number of anchors

The moderate arithmetic and all-order mass budget in main15.11
is now formalized for every fixed positive integer t. Main15.11
moves to in_progress: its saturated-family conclusion and the
general physical relation-to-saturation bridge remain OPEN.
Unconditional numbered coverage86/167, conditional coverage20,
and confirmed improvements132 are unchanged.

MultiAnchorValues uses ACTUAL t distinct offsets in one dyadic
window. The corresponding truncated odd kernels are pairwise
coprime because their prime factors exceed the window width.
Their product Q is squarefree, positive and at most(3N)^t.
For unmarked anchors it exceeds T^t. Every prime factor of Q
belongs to one actual selected value and is larger than Y.
MultiAnchorPrimeBudget proves the literal ceiling bound
m_t=ceil(t*log(3N)/log(Y)) on the number of these primes.

MultiAnchorModuli proves at most t receiving moduli exceed N
whenever their positive product is at most(3N)^t and N>3^t.
This threshold depends only on the FIXED anchor count, never on
the family order. The exact CRT product cost is at most
(6B)^t*2^(r-1)*N^(r-1)/Q. MultiAnchorAssignments obtains this
cost for actual center tuples from the existing prime-assignment
codes and literal congruence fibers; no count is assumed.
The number of assignments is at most(rB)^m_t.

MultiAnchorTupleCover counts the r*N*B^t choices of anchor
coordinate, dyadic center and ordered distinct offsets.
MultiAnchorCertificateCount.HasCertificate requires actual odd
prime membership in the receiving window for EVERY prime of Q.
The finite source tuple bound, uniform in every order r>=1, is
6^t*r*B^(2t)*2^(r-1)*N^r*(rB)^m_t/T^t.
Injectivity is retained and proves the source population is
empty when r>N. The empty-order population is also empty.

MultiAnchorWeightedSeries gives the actual convergent sum over
ALL orders with coefficient a^r/r!. Its finite majorant is
(6^t/2)*B^(m_t+2t)*(m_t+1)!/T^t
times exp(exp(1)*2aN). MultiAnchorOrder proves
m_t*loglog(N)/log(N) tends to t/A for Y=(log N)^A.
MultiAnchorFactorialBudget proves, uniformly for B<=D*log N,
B^(m_t+2t)*(m_t+1)!<=N^(2t/A+epsilon).
The all-order moderate mass is consequently
N^(-t*b+2t/A+epsilon) for T=N^b and any a>=0 with aN<=M.
MultiAnchorCertificateAsymptotic proves this before every
width B and weight a. Its critical-band specialization uses
the exact nominal marginal, with a fixed independent weight.

MultiAnchorFamilyMass recovers the actual factorial divisor by
counting EVERY injective enumeration of each certified family.
Certified means every enumeration has an actual moderate
certificate; it does not assume the desired mass estimate.
The finite layer and all-cardinality inequalities retain
arbitrary nonnegative heterogeneous weights p_x<=a.
MultiAnchorModerateMass.uniform_bound proves their literal
unordered independent product mass is at most
N^(-t*b+2t/A+epsilon), uniformly over every dyadic family
population, all critical-band lengths and all weights bounded
by M/N. No separation, regularity or positive-marginal premise
is used. Contacts and zero weights remain included.

This establishes the moderate certificate calculation with
all quantifiers and factorial costs. The next step must still
construct the t-anchor saturation graph, prove both directed
degrees, and connect actual block-dependent relation witnesses
to the certificate-or-edge alternative. No saturation-tail
bound or completed main15.11 result is claimed here.
No new geometric input, axiom, dependency download, Paper C
port, manuscript-byte change or Palomar registration is made.

Verified under Lean v4.36.0-rc2: full build passed (13289 jobs); direct axiom audit passed for 10143 declarations using only propext, Classical.choice and Quot.sound; all 8457 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 13.44 GiB.


## Unconditional completion of both multi-anchor certificate budgets

Main Lemma15.11 is now complete UNCONDITIONALLY, including
both literal all-order certificate budgets and their connection
to block-dependent physical relation witnesses. It moves from
in_progress to proved. Unconditional numbered coverage rises
from86/167 to87/167; conditional results20 and confirmed
improvements132 are unchanged. No geometric input is used.

MultiAnchorSaturation defines an ACTUAL directed edge x->y:
t distinct offsets in x have a kernel product divisible by D,
where D>6NB, and EVERY true prime factor of D divides a value
in y. Its divisor data prove squarefreeness, prime cardinality
at most m_t, product(D.primeFactors)=D, and large-prime support.
The receiving window's full prime pool has at most B*m_t
members, for every t>=1. There is no abstract edge-degree
hypothesis substituted for the required arithmetic.

MultiAnchorSaturationCounts proves both exact finite covers.
Outgoing centers cost at most B^t*(B+1)^m_t. Incoming centers
cost at most B^t*(t*exp(1)*B)^m_t: every divisor prime is assigned
to an actual selected source offset, while its membership in
the actual receiving prime pool is proved. The bounded-subset
weight inequality handles every prime cardinality, including
the range near the whole pool. MultiAnchorGraph proves its
maximum degree is at most
2*B^t*(2*t*exp(1)*B)^m_t.
MultiAnchorDegreeBudget and MultiAnchorSaturationDegrees prove
the eventual bound N^(t/A+epsilon), simultaneously for both
directed degrees and the actual undirected maximum degree.
One threshold precedes all critical lengths and vertices.

MultiAnchorRelationCertificate chooses t distinct nonzero
coordinates from an ACTUAL physical source word. Prime parity
shows every prime of their truncated kernel product occurs
with odd exponent at a value of some OTHER window. The finite
receiver and offset choices construct a literal assignment
code. If every receiving group modulus is moderate, the tuple
has HasCertificate. Otherwise its oversized group modulus is
a divisor witness for an actual t-anchor saturation edge.
This argument accepts arbitrary contacts and local defects.

MultiAnchorRelationFamilies.Witnesses is the source hypothesis
in literal physical even coordinates: for each UNMARKED block
there is a possibly different family of even coefficient words
whose total parity vector is zero and which selects at least
t values at that block. The witness may depend on the block.
No simultaneous full-support relation is assumed. The words
are reindexed through each actual injective enumeration.
Every noncertified family satisfying these witnesses is
proved admissible in the actual marked saturation graph.
The marks are precisely windows containing a value with
truncated odd kernel at most N^b above Y=(log N)^A.

UniformGraphExponentTail proves a general uniform generator
bound with SEPARATE mark and degree exponents d and q.
For any tilt gamma>0 with d+gamma<=1 and q+2gamma<1, all
admissible families of cardinality at least s have mass at
most N^(-gamma*s+epsilon), under weights<=M/N.
The threshold is chosen before s, every graph and every
family population. It follows from the already proved
positive marked component generator; no desired tail is an
input. The finite denominator and free mark contributions
are bounded explicitly.

MultiAnchorSaturatedMass sets delta=(1-b)*(1-sigma),
theta=t/A and eta=min(delta/4,(1-theta-delta)/2).
The actual marked count is N^(1-delta+eta), and the actual
degree is N^(theta+eta). When theta+delta<1, the general
generator admits the EXACT tilt delta/2, uniformly in s.
Consequently the literal unordered saturated mass is
N^(-s*delta/2+epsilon), with one threshold before ALL s.
Arbitrary nonnegative heterogeneous weights bounded by M/N
are retained. No epsilon times s is lost by moving the tilt.

MultiAnchorBudgets.article_15_11 partitions every actual
witness family into the moderate and noncertified saturated
populations and proves the two printed bounds simultaneously:
N^(-t*b+2*t/A+epsilon) and N^(-s*delta/2+epsilon).
uniform_split_bound also bounds the complete witness-family
mass by their sum. The independent weight per block, true
marginals p_x<=2*nominal_p, contacts, zero weights and irregular
windows are all covered by the more general cap M/N.
The moderate estimate itself was already proved without the
saturated parameter gap; the new theorem preserves that
earlier independent statement.

This completes15.11. It does not yet prove15.12: the ten-core
projection-to-heavy-even-word bridge, quantitative core
peeling, centered activity comparisons and literal primitive
tail remain to be connected. No new mathematical correction
is recorded merely for adding these proofs. No manuscript
byte, dependency, Paper C port or Palomar registration changes.

Verified under Lean v4.36.0-rc2: full build passed (13309 jobs); direct axiom audit passed for 10174 declarations using only propext, Classical.choice and Quot.sound; all 8503 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 13.40 GiB.


## Stronger unconditional primitive tail at all sizes above256

The primitive clause of main15.12 is now proved
UNCONDITIONALLY, with a stronger exponent7/5 instead of4/3.
It includes every cardinality at least256, and proves the
larger actual joint-plus-absolute-centered mass, as well as
the actual heterogeneous rank mass. Main15.12 moves from
not_started to in_progress because its separate CONNECTED
clause remains OPEN. Numbered coverage87/167 and20 conditional
results are unchanged. Confirmed improvement133 records the
stronger primitive tail and its shorter fixed-rank split.

MaximalSupportWord proves an elementary finite coding fact:
some binary codeword has weight at least the code dimension.
Choose a word of maximal support; restriction of the code to
that support is injective, since a nonzero kernel word has
disjoint support and increases the chosen support after
addition. The dimension is bounded by that restriction's
target dimension. For an even code and even t, dimension
at least t-1 therefore yields a word of weight at least t.
No pivot coordinates or simultaneous block support are
assumed or supplied as external data.

PrimitiveCoordinateProjection proves every coordinate
projection of a minimal effective relation kernel is
INJECTIVE. A kernel vector vanishing at that coordinate
restricts to the proper erased family; its nullity zero
forces the restriction to vanish, and extension by zero
recovers the whole vector. Hence every projection image has
dimension equal to the entire primitive nullity.
HeavyPhysicalRelations uses the previously proved
effective_projection_rank_le and the actual surjection
from physical even relations to effective relations.
The coding lemma then constructs an ACTUAL global physical
even relation with at least t selected values at any
prescribed block. PrimitiveAnchorWitnesses consequently
gives the literal15.11 witness predicate whenever
rho>=t-1. Different blocks may use different relations.
In particular every primitive has two-anchor witnesses,
and nullity at least9 gives ten-anchor witnesses.

PrimitiveIndependentBudgets supplies a uniform general
all-cardinality bound from the PROVED15.11 budgets,
using actual independent weights u*p_x and the
unconditional cap p_x<=2*2^C/N. Two explicit specializations
start at cardinality256:
  t=2,A=14,b=59/70,sigma=93/100:
    delta=11/1000, theta=1/7,
    moderate exponent=-7/5,
    saturated exponent=-176/125.
  t=10,A=12,b=31/60,sigma=23/25:
    delta=29/750, theta=5/6,
    moderate exponent=-7/2,
    saturated exponent=-1856/375.
The strict cutoff and graph gaps are verified by exact
rational arithmetic. Both estimates have one threshold
before all sizes, lengths and actual primitive populations.

Primitive256RankTail splits ONLY at the FIXED integer
nullity9. When rho<9, rank amplification is at most2^8=256,
so the two-anchor independent bound gives rank mass
N^(-7/5+epsilon). When rho>=9, the ten-anchor independent
bound applies, and the already proved primitive inequality
rho<=L costs at most2^L<=2^C*N. That branch has the stronger
rank mass N^(-5/2+epsilon). The exact finite filtered sum
then proves the FULL primitive rank mass at every
cardinality at least256 is N^(-7/5+epsilon).
No comparison rho versus a growing fraction of L, no
core deletion, compatibility split, or cardinality upper
cutoff is needed for this primitive argument.

PrimitiveActualMass extends the exact centered-to-rank
comparison to ALL actual marginal patterns. If some actual
marginal is zero, the existing finite probability transport
proves its whole centered coefficient is zero. Otherwise
the actual heterogeneous Fourier inequality applies.
Together with the already proved joint inequality this
gives q(I)+|c(I)|<=2*rankWeight(I), including contacts,
local irregularities, affine incompatibility and zero
marginals. The ground is the FULL dyadic block, with no
regularity filter or separation assumption.

Primitive256Tail.uniform_actual and uniform_centered prove
the stronger all-size exponent7/5. The named
article_15_12_primitive proves the literal printed4/3
bound for all primitive sets of cardinality>256 above
ANY actual ground subset of the dyadic block. It therefore
includes every source-family restriction in the paper.
The independent per-block weight remains fixed before N.
No geometric property, desired arithmetic mass, or new
axiom is an input. The connected part of15.12 is not
claimed, and the all-size T14.2 total still has its recorded
conditional small-size step. No original manuscript byte,
dependency download, Paper C port or Palomar action changes.

Verified under Lean v4.36.0-rc2: full build passed (13327 jobs); direct axiom audit passed for 10193 declarations using only propext, Classical.choice and Quot.sound; all 8524 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 13.36 GiB.


## Constructed relation cores and their actual mass

The actual core construction, exact centered peeling bound,
small-core probability ratio and large-core mass in main15.12
are now formalized UNCONDITIONALLY. These are preparatory
parts of its connected assertion. Main15.12 remains
in_progress: its separate primitive clause is already proved
with stronger power7/5, while the final connected summation
and the required fixed connected activity step remain OPEN.
Numbered coverage87/167, conditional results20 and confirmed
improvements133 are unchanged. No new finding is added for
proving the manuscript's existing core steps.

RelationProjectionRank.loss is the ACTUAL deletion nullity
rho(I)-rho(I erase x). kernel_finrank proves that the kernel
of coordinate projection has exactly the erased nullity:
the finite kernel cardinality is the already exact
missedRelations count, and binary cardinality identifies
its dimension. Rank-nullity then proves
dim(projection_x K(I))+rho(I erase x)=rho(I).
The loss equals the actual effective projection rank.
No ambient finite-dimensionality of the full prime vector
space is required, and no kernel dimension is assumed.

RelationCorePeeling constructs a terminal finite deletion
trace, deleting only blocks of relation projection rank
at most k. Its exact budget is
rho(A)<=rho(D)+k*(card(A)-card(D)).
At termination every remaining projection rank is greater
than k. This differs from the older private-rank peeling:
the new construction deletes SMALL RELATION projections,
which is the direction needed by15.12.
RelationCoreWitnesses.Core t L D uses these exact losses.
exists_ten_core constructs a true ten-core with k=8 and
the exact nullity budget. The previously proved heavy even
word theorem converts each effective projection into an
actual physical relation with ten selected values at that
block; different blocks may use different witnesses.

RelationCoreIndependentBudget.uniform_ten applies the
proved t-anchor budgets to every actual ten-core of
cardinality at least256, giving independent mass
N^(-7/2+epsilon), at ALL cardinalities. The exact parameters
are t=10,A=12,b=31/60,sigma=23/25.
LargeTenCoreMass.uniform_rank includes the ACTUAL nullity
amplification for cores with rho<=2L: it costs at most
2^(2L)=O_C(N^2). Their full rank-weight mass is therefore
N^(-3/2+epsilon). uniform_actual proves the larger actual
q(D)+|c(D)| mass has this same power, including incompatible
and zero-marginal systems. The proof does not assume
primitiveness, separated windows, local regularity or
positive compatibility. It directly supplies the large
ten-core branch needed in15.12.

RelationCoreCounting.full_support_lower proves
(1-card(D)/2^k)*2^rho(D)<=number of full-support relations
whenever each actual projection rank is at least k.
It uses the exact erased-kernel cardinalities and a finite
union bound. half_full_support gives
2^rho(D)<=2*number of full-support relations for every
ten-core of size at most256.
RelationCoreMomentRatio.centered_count transports the
actual compatible infinite-model centered coefficient
to this exact square-class relation count. Together with
the actual joint rank formula, ten_core_ratio proves
q(D)<=2*c(D) for every compatible actual ten-core with
at most256 blocks. There is no common nominal marginal
or hypothetical affine sign prescription.

RelationCoreActivityPeeling.compatible_majorant extends
the actual compatible-nullity centered majorant to every
marginal pattern, including zeros. peeling_bound proves
the literal pointwise activity inequality
|c(I)|<=2^card(I)*2^(k*(card(I)-card(D)))*
        product_{I minus D}(p_x)*q(D)
for any actual compatible maximizing source A and a
constructed k-peeling trace from A to D.
The larger I may be incompatible; every factor is an
ACTUAL marginal or joint probability. The proof uses the
actual maximizing-compatible-nullity equality, the exact
trace budget and the finite product decomposition.
No deletion-order enumeration occurs.
exists_ten_core_bound INTERNALLY chooses the maximizing
compatible A, constructs D, proves q(D)>0, and supplies
the ten-core property, exact rank budget and activity
inequality simultaneously. Neither this core nor its
probability estimate is an external premise.

The remaining connected proof must sum the freely
weighted complements, handle the growing-cardinality
rank retention, and bound the finitely many small cores
using the still-open fixed connected activity estimate.
These verified pieces alone do not establish that final
4/3 bound, T16.2 at all sizes, or the complete stopped law.
No geometric input, new axiom, dependency download,
Paper C port, manuscript byte or Palomar action changes.

Verified under Lean v4.36.0-rc2: full build passed (13343 jobs); direct axiom audit passed for 10213 declarations using only propext, Classical.choice and Quot.sound; all 8547 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 13.33 GiB.


## All-order large-core closure and low compatible nullity

Two complete branches of the CONNECTED argument in main15.12
are now proved UNCONDITIONALLY: arbitrary-cardinality closure
above a large chosen ten-core has mass N^(-3/2+epsilon), and
every connected family of size at least256 with compatible
nullity at most L/60 has mass N^(-83/60+epsilon).
Main15.12 remains in_progress because its small chosen-core
branch still needs the fixed connected activity and pair
deficit assembly. Its separate primitive clause is already
unconditionally proved with stronger power7/5.
Coverage87/167, conditional results20 and confirmed
improvements133 are unchanged.

SeedComplementMass proves the exact finite identity
sum_{D subset I subset G} product_{I minus D}(w_x)
  =product_{G minus D}(1+w_x).
No seed marginal is divided out, so zero weights are allowed.
Its general positive cover theorem allows an ARBITRARY
nonnegative activity c(D) on each seed. If each family
activity is bounded by one seed's activity times its true
independent complement product, the entire family sum is
bounded by exp(sum_G w_x)*sum_D c(D). The finite sum
interchange and actual cover are proved, with no factorial
or deletion-order factor and no family-size cutoff.

ChosenRelationCore.core uses the previously proved existence
theorem to choose an ACTUAL compatible ten-core for every
nonzero length and every original family, including an
incompatible original family. properties supplies its
containment, actual positive joint probability, projection
conditions, exact rank budget and actual activity inequality.
weighted_bound absorbs all fixed powers from peeling into
the single fixed weight512*u. The inequality is
u^card(I)*|c(I)| <= (512u)^card(D)*q(D)*
                   product_{I minus D}(512u*p_x).
All true marginal and joint factors are retained.

LargeCoreFamilyCover.cores is the literal finite population
of actual ten-cores inside G, of size at least256 and raw
nullity at most2L. If the chosen core D of I is large and
rho_*(I)<=2L, its positive probability and containment imply
rho(D)<=rho_*(I), so D really belongs to that population.
finite_bound uses the general complement cover, and
source_mass_le_actual compares its q-weighted seed sum to
the already proved actual core mass q+|c|.
LargeCoreClosureMass.uniform_bound therefore proves
sum_I u^card(I)*|c(I)|<=N^(-3/2+epsilon)
for EVERY actual family population with those chosen-core
properties, at ALL cardinalities. No connectedness or
growing-order cutoff is required for this larger population.
The exact marginal cap bounds the free-complement mean by
a constant before N; its exponential is absorbed only as
a fixed constant. This fully sums the large-core branch,
rather than assuming a propagation or complement estimate.

OriginalTwoAnchorWitnesses proves actual coordinatewise
participation implies projection rank at least one at
EVERY block. The supplied effective relation gives a
nonzero vector in the actual projection image; the exact
projection-rank identity and the physical heavy-word
theorem give the literal two-anchor witness.
Every connected original family of size at least two is
proved to have that property via an actual coordinate
relation. No single relation nonzero at all blocks is
assumed. No coefficient-nonzero or positive-marginal
premise is needed for this connected participation fact.

ConnectedIndependent256Budget.uniform_bound applies the
retuned t=2,A=14,b=59/70,sigma=93/100 certificate budgets.
It proves the ACTUAL independent product mass of every
connected dyadic population of sizes at least256 is
N^(-7/5+epsilon), uniformly at all cardinalities.
LowCompatibleNullityTail.uniform_bound combines that with
the actual compatible-nullity centered majorant, using
weights2*u*p_x. The full maximum rho_* is kept, even for
incompatible I and zero marginal patterns. Under
rho_*(I)<=L/60, the binary rank amplification costs at most
N^(1/60+epsilon). The resulting power is83/60, stronger
than the27/20 low-rank branch in the source proof and
stronger than the required final4/3. This refinement uses
the same two-anchor parameter retuning already recorded
in finding133; no new overall connected theorem is claimed.

The remaining case has a small chosen compatible ten-core.
Its nonempty-rank retention on the growing range,
connectedness forcing a non-direct complement, finite
small-core activity and pair-deficit summation still have
to be assembled. None of those desired arithmetic bounds
is substituted as an external hypothesis here.
No geometric input, axiom, dependency download, Paper C
port, original manuscript byte or Palomar action changes.

Verified under Lean v4.36.0-rc2: full build passed (13357 jobs); direct axiom audit passed for 10227 declarations using only propext, Classical.choice and Quot.sound; all 8563 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 13.30 GiB.


## Exact small-core deficits and the complete pair branch

The exact small chosen-core reduction of main15.12 and its entire
size-two branch are now formalized. The remaining unresolved arithmetic
quantity is the activity of actual small cores of sizes3 through255.
Main15.12 remains in_progress; its primitive clause and two previously
completed connected branches retain their published proofs. Coverage
remains87/167 unconditional,20 conditional,133 confirmed improvements.

SmallCoreRankRetention proves rho(D)>L/120 directly from the exact
chosen-core budget when rho_*(I)>L/60 and |I|<=L/960. Consequently
|D|>=2. If |I|>256 and |D|<256, then D is a proper subset of I;
the actual positive-joint core ratio gives q(D)<=2c(D).
SublogCardinalityCap.uniform_cap derives |I|<=L/960 uniformly from
K_N/log N tending to zero. Its threshold precedes every critical
length. The lower critical-scale estimate retains its true L+1
term, rather than replacing it silently by L.

ConnectedComplementDeficit proves that for ANY nonempty proper
D in a connected I the actual complement I minus D is non-direct
over the true effective span S_D. If it were direct, compressed
nullity equality and restriction would give an additive nullity
split, contradicting actual connectedness. No full-support witness
simultaneously nonzero in every block is postulated.
RestrictedSeedComplements proves a positive finite cover with the
EXACT allowed complement family at each source D. For fixed D,
I maps injectively to I minus D when D is contained in I; the true
allowed complement sum is retained, without a free-complement
exponential, factorial or deletion-order factor.

SmallCoreFamilyCover defines actual positive-joint ten-cores of
sizes2..255 inside G and their joint-weighted non-direct independent
complement sourceMass. The chosen-core activity inequality and the
proved complement cover bound every actual small-core connected
population by sourceMass at the single inflated weight512*u.
The actual small-core ratio converts q(D) into2*|c(D)|, preserving
ALL heterogeneous marginals, including zero-marginal cases.
SmallCoreDeficitReduction.uniform_source then applies the ALREADY
PROVED uniform independent deficit15.6 with source-size cap255.
It proves sourceMass<=2*N^(-1/2+epsilon)*sum_D v^|D|*|c(D)|.
The growing_range_reduction constructs all necessary core size
premises internally, with one threshold before all N,L,G,F.
This is an exact reduction, NOT the final connected4/3 estimate:
its remaining small-core activity has not been assumed bounded.

IndependentDeficitMonotonicity and AllPairDeficitMonotonicity prove
nonnegativity and ground-set monotonicity for the actual independent
and full weighted pair deficits. SmallCorePairDeficit splits the
finite source sum exactly into sizes2 and3..255. Its size-two part
is at most2*v^2*D_2(G,v), with the TRUE full pair deficit D_2.
Its pair_family_bound applies this to every actual connected family
whose chosen core has size2, without any upper cardinality cutoff
or compatible-rank cap. No uniform N^(-1/2) estimate is substituted
for that stronger weighted pair sum.

SmallCorePairMassUnderInputs proves both the source and complete
family size-two contributions are at most N^(-3/2+epsilon).
The proof uses the completed conditional article15.9 theorem;
its finite geometric bundle and all caps remain explicit ordinary
arguments. The common threshold precedes every dyadic subground,
length and actual family population. Thus the pair-core branch is
complete CONDITIONALLY on the SAME existing three geometric
properties; no new desired arithmetic estimate is an input.
The size3..255 activity and final connected-branch assembly remain
open. No new literature property, axiom, dependency download,
Paper C port, original manuscript-byte edit or Palomar action occurs.

Verified under Lean v4.36.0-rc2: full build passed (13377 jobs); direct axiom audit passed for 10250 declarations using only propext, Classical.choice and Quot.sound; all 8588 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 13.26 GiB.


## Positive connected triple seeds with coefficient one

The positive-triple seed step inside main15.10 is now proved with
a stronger coefficient1, replacing the coefficient2 in the source
proof. In fact its stronger TWO-SIDED comparison is proved:
|T3_joint(G)-A3(G)|<=N^(-3/2+epsilon), conditional only on the
same existing finite geometric properties as article11.1.
This does NOT bound A3 itself. Main15.10 moves from not_started
to in_progress; the remaining connected-family seed alternatives,
positive propagation and the printed4/3 remainder remain open.
Coverage87/167 unconditional and20 conditional is unchanged.
Confirmed improvement134 records the stronger finite and asymptotic
comparison for future manuscript integration.

ConnectedTargetDependence proves every member of ANY connected
family with at least two members has a nonzero intersection with
the true effective span of its complement. The existing canonical
coordinate relation supplies a nonzero vector at that member;
RelationCoordinateSpan places it in the complement span. The
other relation coordinates may vanish, so no simultaneous
full-support relation or positive coefficient is assumed.

TripleJointReconstruction proves the literal heterogeneous identity
q(T)=c(T)+sum_(z in T)c(T minus z)*p_z+product_(z in T)p_z
for every actual triple. Its error_bound keeps the exact signed
pair terms before taking absolute values. No primitive/nonprimitive
split, compatibility assumption, regular-site restriction or
positive-marginal premise is required for this identity.

ConnectedTriplePositiveReduction.pair_cost sums these actual
pair terms over ALL connected triples. A nonzero pair coefficient
forces positive pair nullity, even with zero marginals, by the
proved zero-nullity centered cancellation. Connectedness gives
the actual dependent-target condition. The exact distinguished-
member/pair incidence injects this restricted sum into the literal
IndependentTargetDeficit, with no multiplicity constant.
Consequently T3_joint<=A3+D1+M3_independent, with coefficient1.
The same proof gives |T3_joint-C3_signed|<=D1+M3_independent.
Its incompatible_bound controls the incompatible connected triple
activity by this SAME remainder, without any positive-ground
hypothesis. Compatible coefficient nonnegativity then gives
|T3_joint-A3|<=3*(D1+M3_independent).

ConnectedTriplePositiveUnderInputs.uniform_reduction uses the
already proved sharp actual D1 bound15.1/11.1 and the unconditional
connected independent half-count at order3. It obtains
T3_joint<=A3+N^(-3/2+epsilon). Its uniform_absolute_error proves
the stronger absolute-difference statement. The finite chosen-source
surface, ordinary-surface and normalized-curve inputs remain explicit
ordinary arguments at source capepsilon/1024. One threshold precedes
ALL lengths and actual dyadic subgrounds. Zero actual marginals,
contacts and affine incompatibility are retained. The true moving
A3 remains on the right and is not supplied as a bounded premise.
No new external property, axiom, dependency download, Paper C port,
original manuscript-byte edit or Palomar registration is introduced.

Verified under Lean v4.36.0-rc2: full build passed (13385 jobs); direct axiom audit passed for 10261 declarations using only propext, Classical.choice and Quot.sound; all 8599 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 13.23 GiB.


## The complete direct minimal-crossing seed alternative

The complete DIRECT minimal-crossing seed alternative in the proof
of main15.10 is now proved CONDITIONALLY on the same existing three
finite geometric properties. At every fixed target size r>=2,
the actual sum over ALL dependent pairs e and all direct minimal
crossings A of size r is at most N^(-5/3+epsilon).
No desired crossing mass or source host count is an input.
Main15.10 remains in_progress: the remaining internally dependent
crossings (especially the two-pair case), propagation and the
printed full4/3 remainder are not claimed. Coverage87/167,
20 conditional results and134 confirmed improvements are unchanged.

MinimalSpanCrossing constructs an actual inclusion-minimal A
whose effective span meets the old space W. Every proper B has
span DISJOINT from W; B is allowed to have its OWN internal
relations. This differs from minimal relative nullity, which
would also exclude internal relations. Choosing a nonzero
intersection vector and an actual preimage under relation
addition proves a relation nonzero at every target, with a
NONZERO sum in W. The source component is retained explicitly.
MinimalCrossingWindows turns this actual relation into the
already defined coordinatewise relative-window witnesses.
ConnectedSpanCrossing proves every nonempty proper part of an
actual connected family has such a minimal span crossing,
using the exact canonical direct-partition contradiction.

RelativeIntersectionNullity proves the exact generic identity
rho_W(A)=rho(A)+dim(W intersect span(A)). TwoTargetCrossingCut
then proves the precise two-target data for a DIRECT minimal
crossing. After removing two distinct targets y,z, put B for
the other targets and Q=W+span(B). Minimality and directness
prove Q is disjoint from S_y and S_z, and S_y is disjoint
from S_z. The relative nullity is EXACTLY
  dim(Q)+dim(S_y)+dim(S_z)-dim(Q+S_y+S_z).
The old source W may be internally dependent when represented
by its original windows; B may be empty. No primitive property
of the entire original source-plus-target family is assumed.

ExtensionJointFactor proves q(E union A)=q(E)*product_A(p_x)*
2^rho_(S_E)(A) whenever the whole system has positive joint
probability. It proves the corresponding upper bound for EVERY
actual system, including incompatible ones and q(E)=0, without
any division by q(E). DirectCrossingTargets identifies the
printed two-target deficit with the existing actual effective
Kernel dimension and obtains the exact heterogeneous joint
majorant q(e)*product_B(p_x)*p_y*p_z*2^dim(Kernel).

DirectCrossingExtensionsUnderInputs applies the ALREADY PROVED
full dense two-target mass to that actual population. For every
fixed source number it bounds the sum over actual target pairs
by q(e)*product_B(p_x)*N^(-1+epsilon). Pair directness proves
the required nonaligned-or-small-intersection alternative
internally. All eight finite cover/curve arguments are packaged
in the existing Parameters/Hypotheses structure; these are the
same three recorded geometric properties, not a new estimate.
The common threshold precedes every e,B and actual target set.
DenseDirectCrossingFamiliesUnderInputs chooses the two targets
by a proved unordered weighted cover, then sums EVERY choice
of the other sources B. Their true product mass is bounded by
exp(actual_mean), hence a fixed constant; no factorial or host
count is presumed. It proves the ENTIRE dense direct-crossing
family mass above e is at most q(e)*N^(-1+epsilon).

LowCrossingJointMass gives an unconditional complementary
estimate. For every fixed r,s and a>=0, all actual minimal
crossings with relative nullity<=a*L have total joint mass
at most q(e)*N^(-r/2+a+epsilon), uniformly in every source e
of size s and every actual dyadic target subground. This
estimate even allows internal target relations under its
relative rank cap. The actual relative half-count and a
proved critical binary-power bound supply every factor.
DirectCrossingFamiliesUnderInputs splits the direct population
at a=epsilon/4, chosen BEFORE N. Combining low and dense
parts proves the FULL fixed-size direct-crossing mass above
e is at most q(e)*N^(-1+epsilon).

DependentPairJointActivity proves q(e)<=2*|c(e)| on every
actual dependent pair: if q(e)>0 its exact binary rank factor
is at least2 and c(e)=q(e)-product(p_x); if q(e)=0 the
inequality follows directly. The sharp actual pair-activity
bound then proves the full dependent-pair joint sum is
N^(-2/3+epsilon), retaining irregular and zero-probability
pairs. DirectCrossingPairSeedsUnderInputs finally SUMS the
proved source-relative cost over the actual dependent pairs.
The resulting double sum of TRUE joint probabilities is
N^(-5/3+epsilon), at ANY fixed target size at least2 and on
EVERY dyadic subground. The threshold precedes all actual
pair-indexed target populations. Fixed sizes are not replaced
by a growing-order assertion. No external property, axiom,
dependency download, Paper C port, original manuscript-byte
edit or Palomar action is added.

Verified under Lean v4.36.0-rc2: full build passed (13413 jobs); direct axiom audit passed for 10287 declarations using only propext, Classical.choice and Quot.sound; all 8625 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 13.17 GiB.


## Low-intersection two-pair seeds and fixed compatible propagation

The LOW span-intersection two-pair alternative of main15.10,
including propagation to every fixed larger compatible family,
is now proved CONDITIONALLY on the same existing finite geometry.
Main15.10 remains in_progress: dense intersections and its other
remaining primitive/higher-order alternatives are not asserted.
Coverage87/167,20 conditional results and134 confirmed mathematical
improvements remain unchanged.

BlockJointIntersection proves the exact actual two-block identity
q(E union A)=q(E)*q(A)*2^dim(S_E intersect S_A)
whenever the whole system has positive joint probability. For
EVERY actual disjoint E,A it proves the corresponding upper
bound, including incompatible systems and zero source masses.
The proof keeps both exact heterogeneous joint factors and uses
the newly proved relative/internal/intersection nullity identity.
Its finite_bound allows TWO DIFFERENT actual source populations
P,Q and any restricted H subset of P times Q. Under a genuine
pointwise intersection-factor cap K>=0, the actual union joint
sum is at most K*(sum_P q)*(sum_Q q). Positive enlargement and
the finite product-sum identity are proved internally.

LowTwoPairJointMassUnderInputs.uniform_bound applies this to
actual disjoint dependent pairs on every dyadic subground.
If their effective span intersection has dimension at most a*L,
with a>=0 fixed before N, the full actual pair-of-pairs joint
sum is at most N^(-4/3+a+epsilon). Every cardinality, pair-
nullity, disjointness and rank condition refers to the actual
finite population. The completed dependent-pair joint mass
N^(-2/3+epsilon) is used TWICE; the critical binary-power
estimate supplies the intersection factor. There is no input
assuming a pair-of-pairs mass or independent source weights.
The finite geometric cap isepsilon/4096.

LowTwoPairSeeds.sourcePairs defines the literal restricted
pair-of-pairs population. families is its actual union image;
family_data proves every member lies in G and has exactly4
windows. The positive image bound retains all duplicate source
representations safely. LowTwoPairSeedsUnderInputs.uniform_seeds
therefore proves the actual unordered4-window seed joint mass
at the same4/3-a scale, without a canonical pairing assumption.

The existing PROVED unordered positive propagation theorem
then sums every fixed larger family containing one of those
actual seeds. Its true fixed factorial and subpower costs are
absorbed after one common threshold; no propagation estimate
is postulated. uniform_extensions proves actual joint mass
N^(-4/3+a+epsilon) at every fixed order4+k. Compatible
centered coefficients are bounded by their true joint mass
times2^(4+k), yielding uniform_centered_extensions at the SAME
rate. Its compatibility premise is explicit; incompatible
centered families are not dropped from a purported full bound.
Finally uniform_small_intersection_extensions chooses
a=epsilon/2 before N and divides the error margin in half,
obtaining the literal required N^(-4/3+epsilon) compatible
centered bound for this branch. Its finite source cap is
epsilon/65536. The threshold precedes every critical length,
dyadic subground and actual extension population.

This also covers zero span intersection, used when a proper
dependent target pair is direct from the old pair. The dense
strong-alignment pair alternatives remain open. The distinct
fixed/growing-order regimes, actual zero marginals and zero
joint masses are retained. No external property, axiom,
dependency download, Paper C port, original manuscript-byte
edit or Palomar action is added.

Verified under Lean v4.36.0-rc2: full build passed (13421 jobs); direct axiom audit passed for 10298 declarations using only propext, Classical.choice and Quot.sound; all 8638 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 13.15 GiB.


## Dense admissible two-pair seeds and compatible propagation

The DENSE nonaligned-or-weakly-aligned two-pair crossing alternative
of main15.10 is now proved at the true5/3 scale, including every
fixed larger compatible extension. The two new targets are ALLOWED
to depend on each other. This is distinct from the previously
completed direct-target alternative. Main15.10 remains in_progress:
strongly aligned dense crossings and the other remaining primitive
alternatives are not claimed. Coverage87/167,20 conditional results
and134 confirmed improvements remain unchanged.

TwoTargetJointWeight.pair_kernel proves that relative nullity above
ANY actual old-source span, on a pair of distinct targets, equals
the actual three-space Kernel dimension. No target pair directness
is used. intersection_le_kernel bounds the actual source/pair span
intersection by that dimension, retaining internal target nullity.
joint_bound therefore bounds the TRUE joint probability by
q(e)*p_y*p_z*2^dim(Kernel), with both exact heterogeneous target
marginals and the actual source q(e), including zero joint masses.
one_target_bound separately proves q(e union {y,z})<=q(e)*p_y
whenever S_y is direct from S_e. It follows by actual monotonicity
and the zero-intersection block joint bound; no regularity or
nominal marginal replacement is required.

TwoTargetJointMassUnderInputs.uniform_joint applies the completed
dense two-target weighted estimate to actual minimal pair crossings.
Minimality internally proves each target is direct from the old
source. A dense intersection of S_e with S_y+S_z supplies the
required Kernel rank. The admissible alternative is the literal
nonalignment OR small effective S_y/S_z intersection. The threshold
for that intersection is chosen before all N, sources and target
populations. The result is the whole joint target cost
q(e)*N^(-1+epsilon). All existing finite source-surface, ordinary-
surface and curve properties remain ordinary explicit arguments;
no target mass is an input.

DenseAdmissiblePairSeedsUnderInputs sums this proved source-relative
cost over ALL actual dependent old pairs. The already proved full
pair joint mass N^(-2/3+epsilon) gives the TRUE double joint seed
sum N^(-5/3+epsilon), even with internally dependent new targets.
Its two finite geometric parameter bundles are chosen before N;
the pair-bundle source cap isepsilon/2048.

DenseAdmissiblePairSeeds defines the literal dyadic target populations
and their four-window union family. Membership exposes every actual
disjointness, alignment, minimality and intersection condition.
family_data proves size4 and containment in G. A positive union/image
cover retains every source or target representation without an
assumed canonical pairing. DenseAdmissibleSeedFamiliesUnderInputs
proves the actual unordered seed joint bound and propagates it,
using the ALREADY PROVED unordered positive propagation, to every
fixed compatible order4+k. Both its true factorial and2^(4+k)
centered-conversion factors are absorbed as fixed constants. The
complete compatible centered extension sum has rate5/3; its finite
pair-bundle cap isepsilon/8192. All actual marginals, affine
incompatibility and fixed-order quantifiers remain explicit.
No new literature property, axiom, dependency download, Paper C
port, original manuscript-byte edit or Palomar action is added.

Verified under Lean v4.36.0-rc2: full build passed (13431 jobs); direct axiom audit passed for 10309 declarations using only propext, Classical.choice and Quot.sound; all 8651 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 13.12 GiB.


## Complete dense pair crossings including exceptional alignments

The ENTIRE DENSE minimal two-target/pair crossing alternative of
main15.10 is now proved, with the stronger uniform actual seed
rate5/3, including EVERY strongly aligned exceptional normalization.
The source's exchange of exceptional pairs and its final3/2
exceptional-host estimate are unnecessary for this branch.
Improvement135 records this simplification and stronger branch rate.
Main15.10 remains in_progress: its other primitive alternatives,
complete connected-family cover and incompatible part are still
open. Coverage87/167 unconditional and20 conditional is unchanged.
Confirmed mathematical improvements increase from134 to135.

DenseCompressedPairs defines actual dense exact-unit target pairs
and their actual fixed-offset fibers. At each offset pattern the
compressed anchor is INJECTIVE on the original source pairs.
The exact effective block identity identifies the normalized union
space with S_y+S_z, even when it has local relations. Hence the
fiber injects into the ALREADY PROVED dense compressed-center
population. Summing all (L+1)^2 patterns gives a literal finite
pair count bound. No private prime, injective normalization map,
regularity, compatibility or exceptional-pair enumeration is used.
DenseCompressedPairCount consequently proves that ALL dense
actual pairs in ANY fixed channel have cardinality at most N^epsilon,
uniformly over the prescribed old sources and their subspace W.
This counting theorem is UNCONDITIONAL, using the proved15.3 input.

StrongAlignedUnitChannels chooses a finite height cutoff Q after
θ>0 and BEFORE even C or N. The genuinely uniform enlarged aligned
rank theorem implies that every aligned pair with actual effective
intersection rank>θ*L has height at most Q and at least one EXACT
normalized unit. A height larger than Q contradicts the uniform
L/max(a,b) rank cap; zero units contradict the separate full-loss
cap. Both coefficient orientations, height1/2 boundary channels,
irregular windows and nonprivate normalized unions are included.
StrongAlignedDensePairCount covers the whole strongly aligned
population by the fixed finite channel union and its swapped
images. One common threshold for that finite union precedes ALL
actual sources, W and target populations. It proves the full count
is N^epsilon, with no private/good-pair restriction and no geometric
literature input.

StrongAlignedDenseJointMass then uses the exact heterogeneous
one-target bound q(e union {y,z})<=q(e)*p_y, which follows from
minimal crossing and actual source/target directness. The actual
marginal cap p_y<=M(C)/N and the new subpower pair count prove the
ENTIRE strongly aligned dense joint cost is q(e)*N^(-1+epsilon).
This source-relative branch is UNCONDITIONAL, even for internally
dependent old sources and internally dependent new target pairs.
It avoids the need for source/target rank upper bounds involving
nominal regular marginals or for classifying both pairs as exceptional.

DenseTwoTargetJointMassUnderInputs partitions the full dense
minimal pair population into the earlier nonaligned-or-weak
class and its strongly aligned complement. The latter now has
its proved unconditional bound. Thus EVERY dense minimal pair
crossing above any fixed number of actual old windows has joint
mass at most q(e)*N^(-1+epsilon), without any alignment exception.
Only the SAME existing finite source-surface, ordinary-surface
and normalized-curve properties remain explicit theorem arguments
for the first class. No desired mass or pair-count hypothesis is
supplied as an input.

DensePairCrossingSeedsUnderInputs sums that actual source-relative
cost over ALL actual dependent old pairs. The proved sharp pair
joint mass gives the complete dense double joint seed sum
N^(-5/3+epsilon), including the previously exceptional aligned
configurations. DensePairCrossingSeeds defines the full literal
four-window union population, with NO alignment, private, good-edge
or regularity filter. Membership and size4 are proved and duplicate
representations are handled by a positive union/image cover.
DensePairCrossingFamiliesUnderInputs proves the actual unordered
seed joint bound, then propagates it to every fixed larger
compatible order4+k using the already proved positive propagation
and centered-to-joint comparison. The full actual compatible
centered extension rate remains5/3. Fixed factorials and powers
are absorbed after the common threshold. The final pair-bundle
source cap isepsilon/8192; all parameter and quantifier orders
remain explicit. Incompatible centered families are not claimed
bounded by this compatible statement. No new literature property,
axiom, dependency download, Paper C port, original manuscript-byte
edit or Palomar action is added.

Verified under Lean v4.36.0-rc2: full build passed (13449 jobs); direct axiom audit passed for 10324 declarations using only propext, Classical.choice and Quot.sound; all 8671 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 13.08 GiB.


## Isolated-vertex connected triple joint mass

The actual connected-triple branch with an isolated vertex in its
PAIR-dependence graph is now proved at joint-mass rate1, conditionally
on the SAME explicit finite geometric properties. This includes every
primitive triple and every triple with exactly one dependent pair.
An isolated vertex is direct from each of the two other windows taken
separately; it need not be direct from their combined span. No desired
triple-mass estimate is supplied as a theorem input.

ConnectedTripleLowCrossing proves the finite pointwise bound
q(T)<=K*(sum_{x in T}|c(T erase x)|*p_x+prod_{x in T}p_x)
whenever SOME vertex/complement crossing has binary dimension factor
at most K. The exact pair reconstruction, heterogeneous marginals
and positive one-term enlargement are retained, including zero actual
marginals and incompatible systems. Its finite sum is at most
K*(D1+M3_independent_connected), using the proved pair-incidence cost
without any representation multiplicity. The asymptotic version
allows any fixed a>=0 and yields N^(-3/2+a+epsilon) when some actual
crossing dimension is at most a*L. Its pair-geometry source cap is
epsilon/2048. No isolated-vertex assumption is needed for this low
crossing theorem.

RestrictedSingletonPairCover defines the ACTUAL source-specific
fibers F.filter(T=>x in T and R(x,T)). Its weighted positive cover
sums only actual two-target extensions belonging to that fiber.
It does not replace R(x,T) by the weaker existence of another suitable
source. Membership, the cover and exact source erasure are proved.
ProperPairCrossing proves that directness from each target implies
directness from EVERY proper subfamily of that target pair, without
assuming the target pair is internally direct.

IsolatedVertexDenseTripleMassUnderInputs uses those literal fibers
with an actual isolated vertex and crossing dimension>=eta*L. The
completed full dense minimal-pair cost applies above its singleton
source, even when the other two targets are internally dependent.
Summing the actual source marginals uses the proved bounded mean;
a single common threshold precedes all critical lengths, subgrounds,
triples, vertex choices and pair representations. The resulting
actual joint sum is N^(-1+epsilon). IsolatedVertexTripleMassUnderInputs
partitions the whole isolated-vertex triple population at crossing
threshold L/4. The low branch is stronger than rate1; the dense branch
has rate1. Their sum retains rate1 after error absorption. Both finite
parameter bundles and the pair source capepsilon/4096 are explicit.

This is a proved BRANCH, not a bound for all connected triples.
Triples containing at least two dependent pairs remain to be covered.
The printed sharp exponent41/30 of main14.3 is not claimed for this
larger population. Main15.10 remains in_progress, including its
separate sharp primitive-four and full connected-family requirements;
main15.12's connected tail remains open. Coverage87/167 unconditional,
20 conditional and135 confirmed improvements are unchanged. No new
literature property, axiom, dependency download, Paper C port,
manuscript-byte edit or Palomar action is added.

Verified under Lean v4.36.0-rc2: full build passed (13461 jobs); direct axiom audit passed for 10333 declarations using only propext, Classical.choice and Quot.sound; all 8681 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 13.05 GiB.


## Full coarse connected triple joint mass and activity

The ENTIRE actual connected-triple joint mass and absolute centered
activity are now proved at coarse rate1, conditional on the SAME
existing finite geometric properties. This is a new proved ingredient
for the still-open connected-tail reduction. It is weaker than the
paper's sharp41/30 triple rate and does not complete main14.3, main15.10
or the connected clause of main15.12. Coverage87/167 unconditional,
20 conditional and135 confirmed improvements remain unchanged.

StrongAlignedUnitChannels now preserves actual coprimality in
bounded_coprime_channels; its previously published bounded_channels
statement is unchanged and follows by dropping that field. The SAME
uniform rank and exact-unit proof chooses a finite Q BEFORE C or N.
FiniteInteriorUnitEdges defines the actual finite interior coprime
channel set0<a<b<2a, b<=Q and its actual exact-unit pair population.
Every edge lies in the literal dyadic two-subsets. Channel, source,
actual geometric alignment and either endpoint orientation are proved.
Two such distinct edges inside an actual three-element family yield
an exact source unit and a bounded geometric target at either endpoint.
No private-prime, regularity, separation or compatibility filter occurs.
SharedFiniteInteriorTripleMass therefore applies the ALREADY PROVED
EndpointGeometricTripleMass theorem to obtain actual joint mass
N^(-41/30+epsilon) for all such triples, UNCONDITIONALLY.

StrongAlignedInteriorEdges proves every actual strongly aligned pair
outside the1:1 and1:2 boundary channels belongs to that fixed finite
interior unit population. Coefficients are coprime and bounded before
N; actual sorted endpoint geometry excludes the reversed orientation
except for the1:1 boundary. Coprimality identifies equality b=2a with
the1:2 boundary. The common critical threshold controls ALL actual
pairs and lengths. This classification is UNCONDITIONAL.

TriplePairDependence proves a literal three-element family either
has a vertex direct from EACH other window or at least two actual
dependent pairs. In the latter case its vertices are covered by the
actual two-element dependent edges; their true finite union cardinality
forces at least two edges. No probabilistic or geometric assumption
enters this finite exhaustive fact.

CoarseTriplePairSeeds defines the ACTUAL dependent pairs which are
weak, nonaligned,1:1 or1:2 boundary pairs. Membership and a positive
four-population absolute-activity bound are proved. The completed weak,
nonaligned and boundary estimates give their full activity
N^(-1+theta+epsilon). Only the already explicit source-surface,
ordinary-surface and normalized-curve properties enter the nonaligned
branch; no desired pair/triple bound is postulated. The source cap is
epsilon/64. DependentPairSeedPropagation proves actual joint mass of
EVERY fixed containing order is controlled by2*(2+k)!*N^epsilon
times the exact seed activity, using q(e)<=2|c(e)| only for actual
dependent pairs and the proved positive unordered propagation. The
coarse pair-seed extensions keep rate1-theta with source capepsilon/256.

CoarseTripleFiniteReduction proves a COMPLETE cover of ALL actual
three-element dyadic families: an isolated vertex; an actual weak/
nonaligned/boundary dependent-pair seed; or at least two actual edges
from the fixed finite interior unit-channel set. The theorem chooses
Q after theta and BEFORE C,N. Its proof derives every remaining
dependent pair's sorted alignment, true rank>theta*L, boundary
exclusions and exact-unit membership. It assumes none of the desired
mass estimates and is UNCONDITIONAL.

CoarseConnectedTripleJointMassUnderInputs combines this actual cover
with the completed isolated-vertex bound, the pair-seed propagation
and the unconditional finite-channel41/30 bound. Choosingtheta=epsilon/4
before N gives the ENTIRE actual connected triple joint sum
N^(-1+epsilon), uniformly for every subground G and every actual
subpopulation of connected triples. Duplicate representations are
handled by positive union covers. Its independent finite parameter
bundles and source capsepsilon/8192 andepsilon/1024 are explicit.

CoarseConnectedTripleActivityUnderInputs then uses the ALREADY PROVED
two-sided comparison |T3_joint-A3|<=N^(-3/2+epsilon) to bound the FULL
actual connected third absolute centered activity byN^(-1+epsilon).
This includes incompatible systems and zero marginal probabilities;
it does not silently discard them via a compatible-only comparison.
The three pair-bundle source caps areepsilon/16384,epsilon/2048 and
epsilon/2048. All geometric inputs precede a single threshold uniform
in every critical length and actual dyadic subground. No universal
triple-mass, activity, counting or literature conclusion is itself an
assumed hypothesis. The sharp primitive-four branch and the remaining
small-core connected-tail assembly remain OPEN. No new literature
property, axiom, dependency download, Paper C port, manuscript-byte
edit or Palomar action is added.

Verified under Lean v4.36.0-rc2: full build passed (13481 jobs); direct axiom audit passed for 10349 declarations using only propext, Classical.choice and Quot.sound; all 8700 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 13.00 GiB.


## Actual exhaustive seed cover and fixed-range coarse connected mass

Every actual connected family in ANY prescribed fixed range3..R
now has total JOINT mass N^(-1+epsilon), conditionally on a finite
bundle of the SAME existing geometric properties. The matching
coarse compatible absolute centered activity is also proved.
The threshold precedes ALL orders3<=r<=R, all critical lengths,
all dyadic subgrounds and all actual subpopulations. This is a
coarse bound: it does not assert the printed4/3 rate of15.10 or
an incompatible higher-centered bound. Main15.10 and the connected
clause of15.12 remain in_progress. Coverage87/167 unconditional,
20 conditional and135 confirmed improvements are unchanged.

SmallParticipatingConnected constructs an actual effective
relation nonzero at one prescribed coordinate from its genuine
intersection with the span of the other coordinates. It uses
extension by zero and a single-coordinate subtraction, keeping
all effective local kernels. At order at most3, coordinatewise
participation makes the canonical partition connected. This only
requires EACH coordinate to have SOME relation; it does not assume
one simultaneously full-support binary relation. CrossingPairTriple
therefore proves a dependent pair plus an extra window crossing
its span is a connected triple. It also proves every nontrivial
connected family has positive actual relative nullity.

DirectCrossingSeedFamilies defines the literal unordered unions
of a dependent pair and an internally direct minimal crossing of
fixed sizeh>=2. Membership, exact size2+h, ground containment and
a positive double-cover mass bound are proved. The completed
source-relative direct-crossing estimate gives unordered seed
mass N^(-5/3+epsilon), and positive propagation retains this rate
for every fixed containing order. No compatibility is required
for these actual joint bounds. Source caps areepsilon/2048 for
seeds andepsilon/4096 for fixed extensions.

ConnectedSeedCover proves the ENTIRE actual finite combinatorial
cover of a connected I withcard(I)>=3. It contains either a
primitive seed of size>=3; a connected triple; a low-intersection
pair-pair seed; a dense minimal pair-crossing seed; or an internally
direct crossing seed of target size2..card(I)-2. A primitive
subfamily is genuinely extracted. If it is a pair, an actual
minimal crossing to the complement is chosen. Singleton crossings
give connected triples. Internally dependent larger crossings
contain a primitive subfamily: size>=3 returns to the first class;
a proper primitive pair is direct from the source and gives a
zero-intersection pair-pair seed. The remaining pair is split at
its actual span-intersection dimension. Thus proper subfamilies
with INTERNAL relations are retained, and no unproved seed-cover
hypothesis is supplied to an asymptotic theorem.

VariableSeedMassPropagation extends the completed unordered
positive propagation to a SINGLE actual seed population of
VARYING sizes1..r. The actual target population is positively
covered by seed-cardinality fibers. Exact fiber reindexing counts
each source seed once, so only the true fixed target factorialr!
and the chosen subpower factor remain. All source/target masses
are actual heterogeneous joint probabilities, including zeros.

ConnectedSeedCatalog fixes the crossing cutoff atL/12 and collects
all actual seeds needed for orders up toR. Its coverage, actual
ground containment, minimum size3 and positive finite mass bound
are proved. CoarseConnectedParameters is a FINITE parameter bundle:
its hypotheses contain ONLY the existing chosen-source surface,
ordinary surface and normalized curve properties inside the already
recorded Dense/Pair interfaces. It contains no desired activity,
seed mass, connected mass or counting conclusion. The finite lists
and geometric choices precede N.

ConnectedSeedCatalogUnderInputs proves the ENTIRE catalog joint
mass at rate1: primitive seed rate1; connected triple rate1; low
pair-pair rate5/4 at cutoff1/12; dense pair-crossing rate5/3; and
direct-crossing rate5/3. The actual finite channel/order unions
cost at most2*(R+1)+3, which is absorbed after a common threshold.
All geometric bundle source caps are recorded in the Hypotheses
structure and remain finite. There is no order growing with N.

CoarseConnectedJointMassUnderInputs.uniform_range combines this
completed catalog with varying-size propagation. The source
catalog is restricted to actual seed sizes<=r; its full mass bounds
the restricted mass positively. The actual factorialr! is bounded
byR! and absorbed. This proves total actual connected joint mass
N^(-1+epsilon) uniformly for every3<=r<=R, without regularity,
compatibility or positive-marginal restrictions. The separate
uniform_compatible_activity theorem uses the true compatible
centered-to-joint comparison and absorbs2^R, yielding the same
rate for compatible absolute centered activity. Incompatible
higher centered coefficients are not silently excluded from a
purported full statement. The parameter margin isepsilon/4 for
the joint theorem andepsilon/8 for compatible activity. The next
open step is the remaining small compatible relation-core mass
and its connected-tail assembly. No new literature property,
axiom, dependency download, Paper C port, manuscript-byte edit
or Palomar action is added.

Verified under Lean v4.36.0-rc2: full build passed (13501 jobs); direct axiom audit passed for 10367 declarations using only propext, Classical.choice and Quot.sound; all 8723 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 12.95 GiB.


## Completion of both15.12 clauses and stronger connected tail

Main15.12 is now COMPLETE CONDITIONALLY on the SAME existing
finite geometric properties: its entire growing-order connected
clause and its all-cardinality primitive clause are both proved.
The connected clause has the stronger exponent83/60 instead of4/3;
the primitive clause retains its previously proved UNCONDITIONAL
stronger exponent7/5. Finding136 records the full connected
improvement, distinct from the earlier primitive improvement133.
Unconditional numbered coverage remains87/167; conditional results
increase from20 to21. Confirmed improvements increase135 to136.

The connected theorem includes EVERY actual dyadic subground,
fixed positive cardinality weightu, every finite actual connected
population with256<card(I)<=K(N), and true compatible nullity
rho*(I)<=2L. K(N)/log(N)->0 is selected before the common critical
threshold; in the critical band this is the source's K_N=o(L).
The primitive assertion sums every size>256 with NO upper cutoff;
its stronger existing version also includes size256. All marginals,
zero probabilities and incompatible centered coefficients are actual.
No good-source, private-prime, separated or regular-only replacement
is made to the connected population.

DirectBlockDisjoint proves distinct parts of a genuine direct
partition have disjoint effective sum-spaces, using injectivity
of block addition and two single-coordinate tuples. No finite-
dimensional ambient assumption is needed. NoSingletonSeedCover
transfers this to actual canonical component images. Any family
with at least3 vertices and no singleton canonical components
contains a controlled connected seed: either a connected component
of size>=3 contains a seed from the completed catalog, or two
actual canonical pair components form a zero-intersection low
pair-pair seed. The pair components are genuinely dependent and
their actual spaces are direct, with no assumed factorization cost.

The previously proved connected joint-range theorem is strengthened
by exposing uniform_catalog_extensions for ALL actual families
containing catalog seeds. Its older uniform_range and compatible
activity statements remain unchanged. NoSingletonJointMassUnderInputs
therefore proves actual joint mass N^(-1+epsilon) for ALL fixed
orders3..R without singleton components. Its weighted version
sums every size3..R simultaneously, absorbing only fixed powers
and the true finite cardinality-fiber constant. Its finite geometric
bundle is the SAME CoarseConnectedParameters bundle; it does not
assume any desired mass, count or activity conclusion.

SmallCoreJointMassUnderInputs applies this to the actual compatible
ten-cores of sizes3..255. The PROVED ratio q(D)<=2c(D) makes their
centered coefficient nonzero, so their canonical components cannot
be singleton. Their ENTIRE weighted actual joint mass is consequently
N^(-1+epsilon), even when the core is disconnected. This avoids any
need for a sharp fixed higher-centered estimate or for assuming the
full4/3 proposition15.10. Applying the completed UNCONDITIONAL
all-cardinality independent deficit directly to q(D), not to a
surrogate centered activity, proves their actual source-deficit
mass is N^(-3/2+epsilon). The source cap is255 before all actual cores.

SmallCoreSourceMassUnderInputs combines this with the ALREADY PROVED
size-two core branch and the EXACT two/at-least-three source split.
Thus the WHOLE small compatible-core sourceMass has rate3/2.
The exact chosen-core finite cover and retained rank under the
sublogarithmic cardinality cap prove the entire high-rank, small-core
connected branch at rate3/2, uniformly in its actual growing orders.
No enumeration of peeling orders or growing factorial cost is added.

ConnectedTailUnderInputs.uniform_tail now covers the ENTIRE connected
population by low compatible nullity, a large chosen core, and the
remaining high-rank small core. The three PROVED rates are respectively
83/60,3/2 and3/2. Positive actual union bounds and fixed-factor
absorption retain83/60 for their full sum. The low and large-core
branches are unconditional; only the small-core arithmetic uses
the SAME recorded chosen-source surface, ordinary surface and
normalized curve properties, in explicit FINITE parameter bundles.
The final coarse bundle margin isepsilon/64; the pair source caps
are sizeCap((epsilon/128)/128) and sizeCap((epsilon/128)/4096).
Every geometric parameter precedes one N-threshold uniform in
critical lengths, grounds, all orders and all actual families.

ConnectedTailUnderInputs.article_15_12 weakens83/60 to the printed
4/3 and combines it with the separately proved literal all-cardinality
primitive assertion under the same threshold, proving BOTH clauses
of the numbered source proposition. No desired connected or primitive
bound is supplied as an external input. The three geometric literature
properties remain ordinary explicit arguments and are NOT axioms or
claimed internally proved. Main15.10's sharper fixed4/3 assertion,
including primitive-four sharpness and incompatible higher activity,
remains open; it is not needed for this completed tail proof. No
new literature property, dependency download, Paper C port, original
manuscript-byte edit or Palomar action is added.

Verified under Lean v4.36.0-rc2: full build passed (13513 jobs); direct axiom audit passed for 10381 declarations using only propext, Classical.choice and Quot.sound; all 8737 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 12.92 GiB.


## Complete fixed connected centered activity including incompatible systems

CompanionT14.1 is now COMPLETE CONDITIONALLY under the SAME three
explicit finite geometric properties, with a stronger connected
exponent1 instead of4/5. Its separate contact assertion is retained
at rate1 and is UNCONDITIONAL. Finding137 records the stronger full
fixed connected activity. Unconditional coverage remains87/167;
conditional results increase21 to22; confirmed improvements136 to137.

The bound includes EVERY actual connected family at every prescribed
fixed orderr>=3, throughout any fixed range3..R with a common threshold.
Affine incompatibility and zero actual marginals are included. The
actual ground can be any subset of the full dyadic block, so it includes
the source's regular ground. All order cutoffs, finite geometric
parameters and error margins precede N. This is a fixed-order result,
not a bound uniform in an arbitrary order growing with N.

DependentSeedCover defines the actual union of all dependent pairs
and the completed connected seed catalog. It proves every actual
dependent family of size<=R contains one of those seeds, by extracting
a genuine primitive subfamily. It also proves dependent populations
at sizes0 and1 are empty from their actual zero nullity.
FixedDependentJointMassUnderInputs applies the proved varying-size
positive propagation, the sharp actual pair joint mass at rate2/3,
and the complete catalog at rate1. Consequently ALL actual dependent
joint masses in every fixed range2..R have rate2/3. No desired joint
or counting bound is supplied as a hypothesis.

FixedAbsoluteActivityUnderInputs uses the completed exact absolute
centering decomposition. Its independent dependent-family term has
the already proved unconditional rate1; the other terms are actual
dependent joint masses times exact independent complement coefficients.
The bounded actual mean controls those finite coefficients. This
proves FULL absolute centered activity at rate2/3 throughout1..R,
including disconnected, incompatible and irregular families. It uses
the SAME finite geometric bundle and one actual pair-input bundle.

IncompatibleConnectedDeficit proves the exact finite mechanism missing
from a compatible-only argument. When q(I)=0, inverse centering bounds
|c(I)| by the sum of proper centered-source terms. The empty source
is the actual independent product. EVERY nonempty proper sourceD
inside a connectedI has its actual complementI\D in the failed
independent extension population. A proved injective complement
fiber bound handles incidence and duplicate sources without a fake
multiplicity assumption. Thus incompatible activity is at most its
actual independent mass plus the proper-source absolute activity
weighted by the exact all-cardinality independent deficit. This
finite theorem requires no positivity, regularity or geometric input.

IncompatibleConnectedActivityUnderInputs combines that finite bound
with the source rate2/3 and the independently proved complement
deficit rate1/2. The independent connected term has rate at least3/2
at orders>=3. The ENTIRE incompatible connected absolute activity
therefore has rate7/6, uniformly over every fixed range3..R and every
actual subpopulation. All source-cardinality fibers and their fixed
constant are proved. Its geometric margins areepsilon/32 for the
coarse bundle and source capsizeCap(epsilon/32768) for the pair bundle.

CoarseConnectedActivityUnderInputs.uniform_range combines the
completed compatible rate1 with this incompatible rate7/6, using
an exact positive/zero joint split. It proves FULL actual connected
absolute activity N^(-1+epsilon) for every3<=r<=R. The final finite
coarse bundle margins areepsilon/16 andepsilon/64, with pair source
capsizeCap(epsilon/65536). Its companion_T14_1 theorem weakens1 to
the printed4/5 and simultaneously supplies the source's contact
bound from FixedContactCenteredActivity.uniform_bound. The contact
proof needs only the already proved unconditional subpower moments.

The earlier weaker half-power auxiliary estimates under BCN remain
valid historical declarations; they are not inputs to this completion.
Only the recorded chosen-source surface, ordinary surface and
normalized curve properties remain unproved external arguments.
The sharper4/3 assertion of main15.10, its primitive-four sharpness,
and the all-cardinality companionT16.1–T16.3 assertions are not claimed
proved here. No new literature property, axiom, dependency download,
Paper C port, manuscript-byte edit or Palomar action is added.

Verified under Lean v4.36.0-rc2: full build passed (13525 jobs); direct axiom audit passed for 10392 declarations using only propext, Classical.choice and Quot.sound; all 8750 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 12.88 GiB.


## Complete all-cardinality bounded-nullity connected theorem

Companion T16.1 is complete conditionally under the same three explicit
finite geometric inputs. The all-cardinality bound improves from
N^(-min(4/5,2-eta)+epsilon) to N^(-min(1,2-eta)+epsilon).
It holds for every actual subground of the full dyadic block and every
actual connected subpopulation with at least three elements and compatible
nullity at most eta*L. There is no upper cardinality cutoff. The proof in
fact allows every eta>=0; the source's nontrivial decay regime eta<2 is
included. Zero marginals and affine incompatibility are retained.

ConnectedParticipatingWindows.witnesses proves that each coordinate of a
connected family of cardinality at least two participates in an actual
relation. Its relation is allowed to depend on the chosen coordinate.
No simultaneous binary relation with full support is asserted or assumed.

ConnectedBoundedNullityTail.uniform_bound is unconditional. For fixed
eta,u,C,epsilon it selects a fixed integer s and then a common N threshold,
and bounds all actual connected families of cardinality at least s by
N^(-(2-eta)+epsilon). It applies the completed original participating
all-cardinality independent-weight tail to the exact heterogeneous weights
2*u*p_x, whose actual marginal cap is proved. The actual compatible-nullity
majorant contributes at most N^(eta+small margin), proved uniformly from
the critical window band and the actual rank cap. No geometric counting
input or homogeneous substitution for the actual marginals is needed in
this large-cardinality sector.

FixedConnectedWeightedUnderInputs.uniform_bound sums the completed full
fixed connected activity over every order from 3 to a prescribed R. The
weight u^r and the finite number of cardinality fibers are absorbed only
after R and u have been fixed. This includes incompatible systems, using
the completed T14.1 proof rather than a compatible-only estimate.

AllCardinalityConnectedUnderInputs.uniform_bound chooses s from the
unconditional large-cardinality theorem before selecting the finite
geometric parameter bundles for the remaining cardinalities 3<=r<s.
Only after these choices and the explicit geometric hypotheses does it
choose N0. An exact disjoint cardinality split and a fixed-factor
absorption give exponent min(1,2-eta), with one N0 for all actual grounds,
lengths in the critical band and all cardinalities. The final geometric
margins are epsilon/64 and epsilon/256 for two existing coarse parameter
bundles of order s, and sizeCap(epsilon/262144) for the existing pair-input
bundle. These premises are exactly previously recorded geometric
properties, not a desired activity bound. companion_T16_1 supplies the
literal printed exponent min(4/5,2-eta) by monotonicity.

Finding P1-MATH-0138 records the improved exponent and the coordinatewise
participation argument. Unconditional coverage remains 87/167; conditional
coverage increases from 22 to 23; confirmed improvements increase from
137 to 138. T16.2 and T16.3, sharp main15.10 and the final stopped expansion
are not claimed here. No original manuscript byte, external dependency,
axiom or Palomar registration is changed.

Verified under Lean v4.36.0-rc2: full build passed (13533 jobs); direct axiom audit passed for 10397 declarations using only propext, Classical.choice and Quot.sound; all 8755 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 12.86 GiB.


## Complete all-cardinality positive core theorem

Companion T16.2 is complete conditionally, with the stronger positive
joint-mass exponent1 instead of4/5. The bound is uniform over all actual
cardinalities, all actual dyadic subgrounds and all actual t-cores whose
relative nullity lies in (L/2,eta*L]. The source's compatible population is
included; the formal inequality also permits incompatible systems, which
have actual joint mass zero. It holds for even t>=2, eta>=0 and t>=eta+2,
thus includes the source's eta>1 regime without imposing that unnecessary
restriction. Only the same three existing finite geometric properties
remain explicit theorem arguments. No desired mass estimate is a premise.

CoreCanonicalComponents proves that a singleton canonical part forces its
coordinate projection to be the zero linear map, so its exact deletion
nullity loss is zero. Consequently every t-core with t>=2 has only
canonical components of cardinality at least two, with no compatibility or
cardinality restriction. This is a structural statement for actual
square-class relation kernels, not the size<256 ten-core moment ratio.

HighNullityPairMassUnderInputs handles the entire size-two population with
relative nullity>L/2. The proved uniform enlarged alignment rank bound
excludes every aligned coefficient height>=3. Exact orientation and
coprimality leave only the literal1:1 and1:2 boundary populations. Their
full centered activities are already bounded unconditionally at rate1.
The entire nonaligned activity has the existing conditional rate1.
Every dependent pair satisfies actual q<=2|c|, including q=0, so positive
union bounds and a fixed-factor absorption give weighted joint mass rate1
for ALL such high-nullity pairs. No Private, good-source, regularity,
selected-unit or affine-compatibility filter is imposed.

LargePositiveCoreTail proves an unconditional sufficiently large
cardinality rank-mass and joint-mass bound of rate3/2. For arbitrary even
t>=2 it verifies all multi-anchor parameter conditions with A=8t,
beta=1-1/(4t), sigma=1-1/(16t). The moderate independent exponent is exactly
-t+1/2. The positive saturated decay parameter selects a finite size s
before N. Multiplying the completed multi-anchor independent budgets by
the actual relative-rank amplification N^(eta+small margin) gives rate3/2
when t>=eta+2, and the actual joint mass is at most that rank weight. Each
block may use a different actual heavy relation. Heterogeneous marginals,
zero marginals and all actual core populations are retained.

FixedPositiveCoreMassUnderInputs proves joint mass rate1 for every
prescribed bounded cardinality range. Sizes>=3 use the completed actual
no-singleton seed catalog and positive extension propagation; size2 uses
the new high-nullity pair estimate. This avoids an exceptional activation
event and a Holder argument with high count moments. The full
AllCardinalityCoreMassUnderInputs.uniform_bound selects the unconditional
large-cardinality cutoff first, the finite coarse and pair geometric
parameter bundles second, and N0 last. It then combines the finite range
at rate1 with the unconditional rate3/2 tail. Final geometric margins are
epsilon/32 for the coarse bundle and sizeCap(epsilon/256) for the pair
bundle. companion_T16_2 supplies the literal source exponent4/5.

Finding P1-MATH-0139 records the improvement. Unconditional coverage stays
87/167; conditional coverage increases23 to24; confirmed improvements
increase138 to139. T16.3 and the final stopped expansion remain open at
this checkpoint. No original manuscript bytes, dependencies, axioms,
Paper C port or Palomar action are added.

Verified under Lean v4.36.0-rc2: full build passed (13543 jobs); direct axiom audit passed for 10407 declarations using only propext, Classical.choice and Quot.sound; all 8765 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 12.83 GiB.


## Complete connected theorem on the literal linear and growing range

Companion T16.3 is complete conditionally under the same three explicit
finite geometric properties, with exponent1 instead of4/5. The uniform
linear-range theorem keeps the source's full cardinality scope
2*(t-2)*K<=L for any fixed even t>=2 with t>=eta+2. One N0 is chosen before
all admissible critical lengths, all such K, all actual dyadic subgrounds
and all actual connected subpopulations of sizes3..K and compatible
nullity<=eta*L. In particular eta=3/2,t=4 gives the literal K<=L/4 range.
The separate sublogarithmic theorem treats every actual integer schedule
K_N/log(N)->0. companion_T16_3 chooses an adequate even t before N and
supplies the printed exponent4/5 for every eta>=0. No fixed-order estimate
is promoted to a growing-order one.

VariableRelationCore.exists_bound proves the actual compatible peeling
construction at arbitrary t. It first chooses a positive-mass subfamily
attaining the compatible-nullity maximum and applies the proved terminating
trace with deletion threshold t-2. The terminal family is a positive actual
t-core. Its nullity is at most the original compatible maximum, and its
loss budget is at most (t-2)*(|I|-|D|). The already proved actual peeling
majorant includes all coordinates outside the maximizing compatible family,
so incompatible original I and zero marginal sites remain included.
weighted_bound transports the result to exact heterogeneous independent
complement weights with fixed factor 2^(t-1)*u per coordinate.

HighNullityCoreCover defines the entire actual positive t-core population
with relative nullity in (L/2,eta*L]. If rho_*(I)>L and
2*(t-2)*|I|<=L, the proved loss budget forces the terminal core into that
population. The positive supersets bound sums all independently weighted
complements, giving exp(sum_x 2^(t-1)*u*p_x) times the actual core joint mass.
There is no deletion-order factor, factorial multiplicity assumption or
compatibility restriction on the original I. All incidence bounds and
complement reconstruction identities are proved in Lean.

HighNullityClosureUnderInputs combines the completed all-cardinality
positive core rate1 with the proved actual mean cap, which bounds the free
complement exponential by a fixed constant. It therefore controls the
ENTIRE high-compatible-nullity activity at rate1 throughout the literal
linear cardinality range, even without connectedness. Its finite geometric
arguments are the already recorded coarse and pair parameter bundles.

GrowingConnectedUnderInputs.uniform_linear_range splits the actual
connected population at rho_*=L. The low sector uses the completed T16.1
at eta=1, valid at all cardinalities with rate1. The high sector uses the
new actual core closure, also with rate1. A fixed-factor absorption
completes the full connected estimate at one common threshold. The final
low-sector coarse margins are epsilon/128 and epsilon/512, with pair cap
sizeCap(epsilon/524288); the core-sector coarse margin is epsilon/128 and
its pair cap is sizeCap(epsilon/1024). All cutoffs and finite geometric
parameters precede N. uniform_sublog_range derives the literal linear
budget uniformly in every critical length from K_N/log(N)->0, rather than
assuming it silently. The final wrapper explicitly constructs an even t.

Finding P1-MATH-0140 records the stronger growing-range exponent and exact
heterogeneous closure. Unconditional coverage remains87/167; conditional
coverage increases24 to25; confirmed improvements increase139 to140.
T16.1,T16.2,T16.3 are now all complete conditionally. The sharper4/3 fixed
connected main15.10, the exceptional active event T15.2 and the final
stopped expansion are not claimed complete. No new literature premise,
axiom, external dependency, manuscript-byte edit or Palomar action is added.

Verified under Lean v4.36.0-rc2: full build passed (13551 jobs); direct axiom audit passed for 10415 declarations using only propext, Classical.choice and Quot.sound; all 8774 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 12.80 GiB.


## Full fixed absolute activity and the nonconnected quadratic tail

Preparatory progress for main Theorem6.4: full actual absolute centered
activity at every prescribed fixed order>=3 now has rate1, under the same
three existing finite geometric properties. The result is uniform over
every fixed order range3..R and every actual dyadic subground. It includes
all disconnected systems, affine incompatibility and zero marginals.
Main6.4 remains IN PROGRESS: its quadratic factorial-moment correction,
ordinary Touchard correction and all higher factorial cumulants are not
completed by this activity estimate alone. Coverage remains87/167
unconditional and25 conditional; improvements remain140.

BoundedComponentActivity.population is the actual finite ambient candidate
population of all subsets of G with sizes2..R. Its sum_bound proves the
finite cardinality-fiber mass bound. finite_bound controls every actual
nonconnected nonempty family of size<=R by the quadratic positive polymer
tail W^2*exp(W)/2, where W is that population's total absolute centered
activity. The proof restricts to nonzero coefficients, uses actual canonical
components with cardinalities>=2, proves their union recovers the original
family, and applies exact centered factorization. At least two components
are forced by nonconnectedness. No decomposition multiplicity or
independence assumption is supplied as a premise.

NonconnectedActivityUnderInputs.uniform_bound combines this exact finite
bound with the completed all-order coarse absolute mass rate2/3. A fixed
small margin min(epsilon/4,1/12) ensures the component population tends to
zero, so its exponential is bounded by exp(1). The squared mass gives the
FULL nonconnected rate4/3 after absorbing the proved finite-cardinality
constant. Both actual zero coefficients and zero marginal sites remain
included. All cutoffs and margins precede N.

FullFixedActivityUnderInputs.uniform_range makes an exact connected versus
nonconnected split at each order3..R. The connected sector has the completed
rate1, and the nonconnected sector has the new rate4/3. A fixed factor2
absorption gives rate1 for the entire actual absolute centered mass. Only
existing coarse and pair geometric parameter bundles occur as hypotheses;
no target activity estimate or new literature premise is assumed.

This checkpoint adds3 modules,4 theorems and1 definition. It supplies a
finite-order input for the future main6.4 moment correction, without
claiming that correction or a growing-order estimate. No new mathematical
finding, original manuscript-byte edit, dependency download, axiom,
Paper C port or Palomar registration is added.

Verified under Lean v4.36.0-rc2: full build passed (13557 jobs); direct axiom audit passed for 10419 declarations using only propext, Classical.choice and Quot.sound; all 8779 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 12.78 GiB.


## Exact fixed quadratic factorial correction at exponent1

The exact ACTUAL-PARAMETER factorial-moment clause of main Theorem6.4 is
now proved conditionally, with remainder exponent1 instead of4/5. For every
fixed r>=2 it gives E(Z_G)_r=mu_G^r+choose(r,2)*mu_G^(r-2)*a_G+O(N^(-1+epsilon)),
where mu_G is the exact actual heterogeneous mean and a_G is the exact
second factorial cumulant, including its diagonal correction. One threshold
precedes all critical lengths and all actual grounds G contained in the
full dyadic block. No local regularity, separation or affine compatibility
filter is imposed. Only the same three finite geometric properties remain
explicit theorem arguments. Finding P1-MATH-0141 records the improvement.

Main6.4 remains IN PROGRESS because the separate ordinary Touchard correction,
uniform boundedness clause and arbitrary higher factorial cumulants have
not yet been assembled under these geometric inputs. Its optional nominal
parameter reformulation is also not claimed here. Unconditional numbered
coverage remains87/167 and conditional coverage remains25. Confirmed
mathematical improvements increase140 to141. The exact factorial clause is
not counted as the whole multi-conclusion numbered theorem.

ElementarySymmetricApproximation proves the actual collision error without
replacing the individual marginals by a common probability. Its pointed
incidence identity expresses (r+1)*e_(r+1) as the sum over r-element sets of
their actual product times the sum of weights outside that set. The exact
factorial increment and induction give 0<=mu^r-r!*e_r<=r^2*kappa*M^r when
all weights are nonnegative, individually<=kappa, and the mean<=M with
M>=1. The raw elementary error follows by division by r!, and deletion of
at most s actual indices adds only s*r*kappa*M^r. These are finite real
inequalities at every order, proved with all repeated-index contributions.

QuadraticMomentApproximation isolates the exact cardinality0,1,2 layers
of the actual inverse-centering convolution. The empty layer is the actual
elementary independent weight, the singleton layer vanishes, and the pair
layer retains its actual complementary elementary weight. The entire higher
layer is bounded by M^r times the sum of ALL absolute centered coefficients
at orders3..r. The deletion estimate controls the pair-layer replacement by
the full actual mean. The proved factorial/choose identity supplies exactly
choose(r,2). The diagonal sum of individual squared marginals is retained,
yielding the actual second factorial cumulant rather than a distinct-index
covariance approximation. The resulting finite error is explicit in kappa,
the full pair absolute activity and the full higher-order activity. No
probabilistic or arithmetic conclusion is supplied as a hypothesis.

SubpowerPairAbsoluteActivity proves an unconditional subpolynomial bound
for the ENTIRE absolute pair activity. It uses the already proved actual
joint-mass subpower bound and the independently bounded actual mean. Zero
marginals and incompatible pairs are included. This weak input suffices
because the pair-layer deletion error contains an extra factor kappa=O(1/N).

FixedQuadraticFactorialMomentsUnderInputs combines the complete higher
absolute activity rate1 with the unconditional pair subpower bound, actual
marginal cap and actual mean cap. It instantiates the finite quadratic
inequality, transports the exact subset moment to the actual infinite-law
factorial moment and identifies the full second factorial cumulant using
the proved heterogeneous covariance formula. All finite r-dependent
constants are absorbed after r is fixed. The final coarse geometric margins
are epsilon/128 and epsilon/512, with pair capsizeCap(epsilon/524288);
the nonconnected coarse margin is min(epsilon/32,1/12)/8, with its existing
pair capsizeCap(min(epsilon/32,1/12)/8192). These are existing finite input
properties, selected before N. No BCN premise or target moment bound is used.

This checkpoint adds4 modules and13 theorems. No original manuscript byte,
external dependency, new axiom, Paper C port or Palomar registration changes.

Verified under Lean v4.36.0-rc2: full build passed (13565 jobs); direct axiom audit passed for 10432 declarations using only propext, Classical.choice and Quot.sound; all 8792 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 12.76 GiB.


## Exact ordinary fixed correction and bounded count moments

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

Verified under Lean v4.36.0-rc2: full build passed (13577 jobs); direct axiom audit passed for 10445 declarations using only propext, Classical.choice and Quot.sound; all 8808 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 12.72 GiB.


## Complete main Theorem6.4 at the stronger scalar exponent1

Main Theorem6.4 is now COMPLETE CONDITIONALLY under only the same three
explicit finite geometric properties. ALL literal conclusions are proved:
the exact actual-mean/full-second-cumulant factorial correction, its optional
nominal-mean/nominal-second-correction reformulation, uniform boundedness of
every fixed ordinary moment, the genuine Poisson Touchard second-derivative
ordinary correction, and every actual factorial cumulant of fixed order>=3.
ALL scalar remainders improve from exponent4/5 to exponent1. Finding141 is
extended to the complete theorem without incrementing the improvement count.
Unconditional coverage remains87/167; conditional results increase25 to26;
confirmed mathematical improvements remain141.

Every actual-parameter conclusion holds on every actual subground of the
full dyadic block, with exact heterogeneous marginals, zero marginals and
affine incompatibility included. The nominal reformulation concerns the
full original count, as in the source. Every order, finite collection of
geometric parameter bundles and fixed constant is selected before N. No
claim uniform in an order growing with N is made. Earlier BCN-dependent
auxiliary estimates are retained as historical preparatory declarations;
they are NOT inputs to this completion. Its only unproved mathematical
arguments are the chosen-source surface cover, ordinary surface cover and
normalized curve uniformity already recorded in the literature ledger.

The previously completed fixed factorial correction at exponent1 uses the
full higher centered activity and exact heterogeneous collision/deletion
bounds, retaining the squared-marginal diagonal term in the actual second
factorial cumulant. The completed ordinary correction transports the exact
Stirling identity to the actual count, identifies the genuine Poisson
Touchard polynomial and differentiates that polynomial twice. The proved
actual second-cumulant rate2/3 and actual mean cap give uniform boundedness
of all fixed factorial and ordinary moments without the final law
approximation; orders0 and1 are separately unconditional.

FormalFactorialCumulants supplies the missing ALL-ORDER definition and
algebra. Its cumulants are r! times coefficient r of the actual formal
logOf series, rather than a recursively named substitute. Substituting the
proved derivative of log(1+X) gives derivative(logOf f)*f=derivative(f) for
constant coefficient1. Extracting coefficients, multiplying by factorials
and proving the exact choose/factorial identity yields the complete
moment-cumulant recurrence. It proves the order0,1,2 formulas and the full
order3 and4 formulas. No logarithm, derivative or cumulant identity is
assumed as an external input.

AllFactorialCumulants constructs the actual factorial generating series
from E(Z_G)_r/r!. Its coefficient is proved equal to the actual r-subset
joint-mass sum, and its constant coefficient is proved1. The formal moments
recover the actual infinite-law factorial moments at every order. The
logarithmic cumulants have first coefficient equal to the actual mean and
second coefficient equal to the full actual second factorial cumulant.
Its third and fourth coefficients are proved exactly equal to the existing
complete heterogeneous third and fourth cumulants. The actual all-order
recurrence is transported from the formal logarithm theorem.

QuadraticMomentRecurrence isolates the first two cumulants in that recurrence.
The quadratic moment model has zero order3 residual. At every order n>=4
its exact residual is -(n-1)*choose(n-2,2)*mu^(n-4)*a^2. This identity is
proved algebraically, with all natural-index boundary cases. The module also
proves uniform finite moment envelopes and the residual bound on bounded
nonnegative means.

QuadraticCumulantBound.Data is FINITE ALGEBRAIC DATA, used only inside the
proof: exact mean and second cumulant, common quadratic moment error tau,
0<=tau<=1 and a^2<=tau. It is not an external geometric hypothesis. Its
proved step_bound controls the current cumulant by previous cumulants,
explicit finite moment envelopes and the quadratic residual. The exact
budget is nonnegative. FiniteCumulantControl proves by strong induction that
for each fixed r>=3 and mean cap M there is a constant B, chosen BEFORE the
series and tau, with |kappa_r|<=B*tau. All earlier-cumulant budgets and their
finite index ranges are proved; no higher cumulant bound is supplied as an
unproved premise.

FixedHigherCumulantsUnderInputs DISCHARGES EVERY FIELD of that finite data
for the actual count. It selects the finite geometric bundles for the
already proved factorial corrections at all orders up to r. With
 delta=min(epsilon/4,1/4), tau=N^(-1+delta),
the unconditional mean cap gives M, the proved second-cumulant rate2/3 gives
a^2<=N^(-4/3+delta)<=tau, and the full fixed factorial correction supplies
every moment error. Orders0 and1 are exact. A common threshold precedes all
actual subgrounds and lengths. The finite cumulant constant is absorbed to
give |kappa_r|<=N^(-1+epsilon) for every prescribed r>=3. The geometric
premises are precisely the existing FixedMomentInputs bundles at margin
delta and one finite pair bundle with source capsizeCap(1/100). No desired
moment, cumulant or activity estimate is an external argument.

NominalQuadraticFactorialMomentsUnderInputs proves the source's optional
nominal reformulation at the SAME improved rate1. The exact nominal second
correction differs from the actual second cumulant by mu^2-lambda^2. The
unconditional fixed power-mean bias bounds handle orders r,r-2 and2; the
proved actual second-cumulant decay makes the quadratic parameter bounded.
A fully proved finite parameter-change identity and fixed-factor absorption
then give the nominal factorial correction. The reused power-mean bias
lemma is itself unconditional even though its historical module also
contains separate BCN-dependent results. No BCN hypothesis enters this
proof.

This completion adds7 modules,37 theorems and9 definitions/structures, with
selected Mathlib formal-logarithm imports under the pinned compiler and
Mathlib commit. No new unproved literature property, axiom, dependency
download, original manuscript byte, Paper C port or Palomar action is added.
The sharper4/3 law and moment remainders later in the paper remain separate
work; the complete fixed-order Theorem6.4 is now proved at the stronger
intermediate power1 without using that later approximation.

Verified under Lean v4.36.0-rc2: full build passed (13599 jobs); direct axiom audit passed for 10482 declarations using only propext, Classical.choice and Quot.sound; all 8854 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 12.70 GiB.


## Stronger joint-plus-absolute all-cardinality connected activity

Companion T16.1 is strengthened again: the SAME all-cardinality exponent
min(1,2-eta) now bounds the strictly larger actual joint-plus-absolute-
centered sum, not just the centered absolute activity. The result holds on
every actual dyadic subground for every connected family with at least three
members and compatible nullity<=eta*L. All cardinalities share one threshold.
Affine incompatibility and zero marginals remain included. The source's
0<=eta<2 decay regime is included; the inequality is also valid for eta>=2.
Finding P1-MATH-0142 records the larger quantity. Coverage stays87/167
unconditional and26 conditional; confirmed improvements increase141 to142.

CompatibleJointMajorant.pointwise proves the exact actual joint majorant
q(I)<=prod(p_x)*2^rho_*(I), with no cardinality-dependent factor. When q(I)>0,
the exact actual joint rank formula and equality rho_*=rho give the result.
When q(I)=0 the majorant is nonnegative. weighted_bound proves the finite
weighted sum version with the actual individual marginals and any proved
uniform compatible-rank amplification. No rank weight is silently
identified with an incompatible affine probability.

FixedConnectedJointWeightedUnderInputs proves weighted joint rate1 over
every prescribed finite order range3..R. Connectedness gives an actual
positive projection at every coordinate; hence no canonical component is
a singleton. The completed no-singleton joint catalog estimate then applies.
Its only hypotheses are the existing finite coarse geometric parameters,
at margin epsilon/8, selected before N.

ConnectedJointBoundedNullityTail gives the UNCONDITIONAL sufficiently large
cardinality joint tail at exponent2-eta. The actual compatible joint
majorant is multiplied by the completed original participating independent
weight tail, using exact weights u*p_x and their proved uniform marginal
cap. Each coordinate may have a different relation witness; no simultaneous
full-support binary relation or edge-independence assertion is assumed.
The cutoff is chosen before the threshold and all cardinalities are retained.

AllCardinalityConnectedJointUnderInputs.uniform_bound combines that tail
with the finite weighted joint range, yielding min(1,2-eta) at all actual
cardinalities, with one existing coarse bundle at margin epsilon/16.
AllCardinalityTotalActivityUnderInputs.uniform_bound combines it with the
already completed all-cardinality absolute centered bound. It proves the
larger sum of u^|I|*(q(I)+|c(I)|) at exponent min(1,2-eta). Final finite
geometric margins are epsilon/128 and epsilon/512 for the centered coarse
bundles, sizeCap(epsilon/524288) for their existing pair bundle, and
epsilon/32 for the joint coarse bundle. The finite union of these arguments
uses only the same three already recorded geometric properties.

This stronger positive quantity is useful for activation events and for
families obtained after compressing a dependent pair. Those applications
are still separate work, and the distinct separated compressed exponents
in T15.1 are not asserted here. This checkpoint adds5 modules and6 theorems.
No new unproved literature property, axiom, dependency download, original
manuscript edit, Paper C port or Palomar registration is added.

Verified under Lean v4.36.0-rc2: full build passed (13609 jobs); direct axiom audit passed for 10488 declarations using only propext, Classical.choice and Quot.sound; all 8860 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 12.67 GiB.


## Whole compressed-pair mass at all cardinalities

The WHOLE, unseparated clause of companion T15.1 is now proved at its
literal exponent1 under only the same three existing finite geometric
properties. The proof actually covers EVERY actual dependent source pair,
not only pairs in channels2:3 and3:4. For every fixed u>0 and epsilon>0,
parameters are selected before their explicit geometric hypotheses, then
one threshold is selected before N,L, every actual dyadic subground G and
EVERY subpopulation of actual primitive compressed extensions. The sum is

  sum_(e,A) u^(|A|+2) [ q(e union A) + |compressed_c(e,A)| + |c(e union A)| ]
       <= N^(-1+epsilon).

The source pair remains distinguished in this sum. All cardinalities,
nonempty targets, heterogeneous actual marginals, affine incompatibility
and zero marginals are retained. The new finite theorem proves the
coefficient really is the expectation of the centered source INDICATOR
as one block times the centered individual target indicators. Its exact
primitive value is q(e union A)-q(e)*prod_(x in A) p_x, including incompatible
configurations. It is not a homogeneous rank weight treated as a joint
probability or a product of separately centered source endpoints.

PrimitiveCompressionCriterion.primitive_iff proves the exact equivalence
between primitiveness of the actual augmented effective-space family on
{none} union some(A), with EVERY proper subfamily direct, and the explicit
criterion: A is internally direct, relative compressed nullity is positive,
and every proper target subfamily has zero compressed nullity. The internal
directness clause accounts for deletion of the compressed source block.
PairPrimitiveCompression.primitive_iff_augmented specializes this equivalence.
The population also requires the actual source and target index sets disjoint.

RelationLossMonotonicity proves actual deletion-loss monotonicity by zero
extension of relation kernels and inclusion of their coordinate projection
ranges, without a finite-dimensional ambient-space assumption. For a source
pair, its deletion loss equals its nullity. For a target in a primitive
compressed extension, the deletion loss of the original union equals the
compressed nullity. Thus source nullity and compressed nullity are EACH
at most L. Canonical connectedness of the original union is proved: both
source endpoints must lie in one canonical block because their intersection
has positive dimension; any other block would be an internally dependent
subfamily of the internally direct target set.

The original union has the following exhaustive rank dichotomy. If either
source or compressed nullity is at most2, total actual nullity is at most
L+2. Otherwise every original coordinate has deletion loss at least3, so
the union is an actual4-core with total actual nullity at most2L.
ConnectedOneRankOffsetMassUnderInputs proves all-cardinality joint-plus-
absolute-centered mass rate1 below L+2 by the completed bounded-compatible-
nullity theorem with eta=1+epsilon/4. ConnectedFourCoreMassUnderInputs
proves the same rate for all connected4-cores below2L: its large-cardinality
rank tail has unconditional rate3/2 and its finite range has the completed
connected rate1. Neither sector assumes the desired compressed estimate.

DistinguishedPairWeights.fiber_card bounds the ACTUAL number of source
choices for any fixed original union by2^|I|; disjointness makes its target
set uniquely I minus the source. weighted_bound absorbs this multiplicity
by replacing u by2u, retaining every distinguished pair. The compressed
coefficient adds the product term q(e)*prod_A p_x. Each actual primitive
target belongs to the existing source-relative independent deficit family;
q(e)<=2|c(e)| for every dependent pair. Consequently the full source-product
mass is at most2*u^2 times the already completed all-pair deficit, of rate3/2.
The finite full-mass comparison is proved before the arithmetic estimates.

CompressedPairMassUnderInputs.Parameters and Hypotheses are finite bundles
of the SAME ordinary/source surface covers and normalized-curve bounds.
The low-rank coarse margins are epsilon/512, epsilon/2048, epsilon/128,
with pair cap sizeCap(epsilon/2097152). The4-core margins are epsilon/128,
epsilon/512, epsilon/32, with pair cap sizeCap(epsilon/524288). The initial
and finite-order deficit caps are sizeCap(epsilon/4096) and
sizeCap(epsilon/131072). All bundles are ordinary explicit theorem arguments;
no BCN or new unformalized property is introduced. Their finite union has
one threshold independent of the actual ground set, subpopulation and size.

Finding P1-MATH-0143 records the broader all-dependent-pair domain and the
alternative proof of the whole clause. The SEPARATED exponents4/3 and5/4
in the first clause of T15.1 remain open. Therefore T15.1 changes only from
not_started to in_progress; it is NOT counted as a conditional completion.
The homogeneous rank-weight pair-target estimates in T1.12(ii) also remain
open. This checkpoint adds9 modules,36 theorems,6 definitions and2 finite
parameter structures. Coverage remains87/167 unconditional and26 conditional;
confirmed improvements increase142 to143. No original source byte, Paper C
port, dependency download, hidden axiom or Palomar registration is added.

Verified under Lean v4.36.0-rc2: full build passed (13627 jobs); direct axiom audit passed for 10524 declarations using only propext, Classical.choice and Quot.sound; all 8904 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 12.63 GiB.


## Complete actual retained exceptional event, companion T15.2

Companion T15.2 is now COMPLETE CONDITIONALLY, with its literal actual
measurable exceptional event of probability at most N^(-4/5+epsilon), its
actual direct sum of singletons and at most one compressed good-pair space,
and the explicit bound rho(I)<=L/3+1 for EVERY active subfamily I outside
the event. The same event also gives actual original/modified law total
variation at most N^(-4/5+epsilon). Parameters are chosen before the existing
geometric hypotheses, then one threshold before N,L and EVERY actual dyadic
subground G. The retained good-pair threshold is explicitly H=8*(L+1).
The retained count is the actual count off the event and zero on the event;
its law and the original law are actual normalized probability measures.

NongoodPairSeeds proves that the finite compatible private good partition
at channel cutoff Q=4 is contained in the actual retained goodEdges class.
Only its two possible channels2:3 and3:4 occur; the exact source order and
positive effective pair intersection are proved from the actual pair data.
Every dependent nongood pair therefore belongs to the height-five weak tail
or the finite exceptional class. DependentPairJointActivity gives q(e)<=2|c(e)|
without assuming affine compatibility or positive marginals. The completed
height-five aligned tail has rate4/5 and the existing finite exceptional
class has rate1. NongoodPairJointMassUnderInputs.uniform_bound proves the
whole POSITIVE joint nongood seed sum at the literal rate4/5, uniformly on
all actual dyadic subgrounds, under one existing finite pair bundle with
cap sizeCap(epsilon/128). No desired exceptional-event estimate is assumed.

TwoDependentPairSeeds proves that the union of ANY two disjoint actual
dependent pairs has exactly4 members and every coordinate has positive
deletion loss, by the proved loss monotonicity. It therefore has no
singleton canonical component. The completed fixed no-singleton joint
bound gives its entire actual joint seed sum rate1. This includes
unseparated pairs and arbitrary intersections of their effective spaces;
it does not assume the sharper separated homogeneous two-pair theorem.

RetainedActivationSeeds.cover proves an EXHAUSTIVE finite cover of every
nonretained family at EVERY cardinality by just four positive seed types:
(1) a dependent nongood pair; (2) an original primitive family of at least
three sites; (3) two disjoint dependent pairs; or (4) an actual primitive
compressed extension of a distinguished dependent pair. Extract a minimal
original dependence. A good pair e can be compressed. If the whole family
is not retained, some minimal target set A has positive compressed nullity.
If A is internally direct, it is exactly a primitive compressed extension.
Otherwise extract an original primitive inside A: it either has at least
three sites or is a dependent pair disjoint from e. This dichotomy closes
the finite proof without dropping nonpositive or incompatible configurations.
Each selected seed is proved contained in the original actual ground set.

The exact original-model event of nonretention is contained in activation
of this finite seed family. Actual measure monotonicity and the proved
finite-cylinder activation bound give its probability at most the positive
joint seed sum. Repeated seeds are handled by nonnegative finite union
bounds. The compressed image sum is bounded by the completed three-term
compressed mass with the distinguished pair retained, at fixed weight1.
The all-cardinality original primitive rate1 is passed from its actual
rank majorant, including zero marginals, with no regular-ground restriction.
The four positive estimates share one threshold, giving rate4/5. A separate
contact exclusion is not needed for the stated retained direct-sum conclusion.

RetainedExceptionalEventUnderInputs.companion_T15_2 sets E to the literal
nonretention event. Its measurability is proved via the existing actual
finite-cylinder realization. Outside E, the conclusion is explicitly the
injectivity of the singleton-space addition map OR a retained good pair
e and injectivity of the compressed-space addition map. The existing
retained-subfamily theorem supplies rho(I)<=L/3+1 for every active I.
uniform_totalVariation uses the already proved actual coupling; no retained
signed reference is called a probability law.

RetainedExceptionalEventUnderInputs.Parameters is a finite combination of
the completed compressed-pair parameters, one nongood pair bundle, one
order4 coarse bundle and finitely many original primitive bundles. Its
Hypotheses use nongood cap sizeCap(epsilon/256), order4 margin epsilon/8,
compressed hypotheses at epsilon/2 and the same original primitive inputs.
Only the SAME three recorded geometric properties are ordinary explicit
arguments. No BCN plane estimate or additional unformalized property enters
the completed proof. Earlier BCN qualitative preparations remain historical
declarations; their weak convergence estimate is not used for this rate.

Finding P1-MATH-0144 records the simpler exhaustive positive-seed route,
which uses neither a separate contact exclusion nor the still-open sharp
separated homogeneous estimates, together with the actual quantitative
law-coupling consequence. T15.1 remains in progress because its separated
exponents4/3 and5/4 are open; T1.12(ii)/(iii) homogeneous rank-weight clauses
also remain open. This checkpoint adds6 modules,18 theorems,4 definitions
and2 finite parameter structures. Coverage is87/167 unconditional and27
conditional, with144 confirmed mathematical improvements. No original
manuscript bytes, Paper C port, dependency download, hidden axiom or Palomar
registration is added.

Verified under Lean v4.36.0-rc2: full build passed (13639 jobs); direct axiom audit passed for 10542 declarations using only propext, Classical.choice and Quot.sound; all 8928 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 12.59 GiB.


## Complete modified count and every-order bounds, companion T19.3

Companion T19.3 is now COMPLETE CONDITIONALLY, including restoration
from the actual regular-ground count to the full original dyadic count.
The modified count is constructed on the SAME original infinite prime-sign
space: it equals the regular-ground count when its active configuration is
retained at threshold H=8*(L+1), and zero on the actual nonretention event.
The original and modified laws are actual normalized probability measures,
identified with the pushforwards of those random variables.

ModifiedCountAllTailsUnderInputs.companion_T19_3 selects its finite geometric
parameters before their ordinary hypotheses, and ONE threshold before N,L
and EVERY natural tail order k>=1, factorial order r>=1 and real s>=1.
For the actual regular ground G, n=|G|, p=2^(-L) and mu=n*p, it gives ALL
of the source conclusions together:

  TV(Law(full original count),Law(modified regular count))<=N^(-4/5+epsilon),
  delta=P(actual nonretention on G)<=N^(-4/5+epsilon),
  P(regular count>=k)<=mu^(k-1)/(k-1)!+delta,
  P(modified count>=k)<=mu^(k-1)/(k-1)!,
  E s^modified<=s*(1+p*(s-1))^n,
  E s^modified<=s*exp((s-1)*mu),
  E(modified)_r<=mu^r+r*mu^(r-1).

The all-order inequalities themselves were already proved UNCONDITIONALLY
for the actual direct maximum R and shifted envelope R+1, followed by the
pointwise domination modified<=R+1. Their tail probabilities, finite-cylinder
realizations, observable integrability, binomial subset counts and full
nonnegative subset generator are all actual checked theorems. No fixed-order
asymptotic constant is reused at growing order. The exact falling-factorial
shift retains its repeated-index term r*mu^(r-1). Zero means, empty grounds
and orders beyond the ground size are included by those finite results.

OriginalCountLawCoupling.finite_law proves invariance of the actual count
law under every sufficiently large finite observation cutoff. A common
finite cylinder therefore proves the coupling of actual count laws on
arbitrary finite grounds by their actual disagreement probability.
restore_modified composes this with the actual retained-modification
coupling. The existing unconditional regular-ground restoration error is
O_C(N^(-1+epsilon/2)), while the newly completed literal exceptional event
has exponent4/5. Their sum is absorbed uniformly into N^(-4/5+epsilon).
Thus the TV conclusion is for the FULL original count, rather than only
the already regularized count.

The same earlier heterogeneous envelope statements remain valid on ANY
actual finite ground: replace p^|I| by the product of exact p_x, mu by
sum p_x and the binomial generator by product(1+(s-1)*p_x). In particular,
local affine incompatibility and zero marginals were handled explicitly.
The source regular-ground formulas are obtained by the proved exact
regular marginal identity. No exponential estimate for the full original
count on the exceptional event is asserted; the exponential and factorial
tails here concern the constructed modified variable.

The only unproved inputs for the numerical4/5 coupling rate are the same
three finite geometric properties used in the completed T15.2. They occur
as RetainedExceptionalEventUnderInputs.Hypotheses at epsilon/2. No BCN
plane bound or new unformalized property occurs in the completed proof.
Earlier qualitative BCN preparations remain historical declarations; the
new theorem supplies the literal rate and every-order quantifier order.
No new mathematical finding is added: this completes the missing event
and original-law restoration clauses of the existing T19.3 development.
The existing improvement88 in its ledger remains recorded with its
original validation history.

This checkpoint adds2 modules and5 theorems, with no new definitions or
inputs. Coverage is87/167 unconditional and28 conditional, with144 confirmed
improvements. T15.1 sharp separated clauses and the optimal quadratic-law
rates remain open. No original manuscript bytes, Paper C port, dependency
download, hidden axiom or Palomar registration is added.

Verified under Lean v4.36.0-rc2: full build passed (13643 jobs); direct axiom audit passed for 10547 declarations using only propext, Classical.choice and Quot.sound; all 8933 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 12.57 GiB.


## Complete positive mass outside the retained class, companion T17.3

Companion T17.3 is now COMPLETE CONDITIONALLY, including BOTH its exact
finite positive-boundary inequality and its uniform rate4/5 over the literal
linear range4K<=L. For H=8*(L+1), G=regularStarts(N,L), mu=E Z_G and the
literal actual nonretained low-nullity sum R_K, the checked statements are

  R_K <= F + Gdef + exp(2mu) * [ exp(A_good+A_bad+B_K)-1-A_good ],
  R_K <= N^(-4/5+epsilon), uniformly over every4K<=L.

F and Gdef are the previously constructed literal independent deficits,
with their exact cardinality grouping. A_good=4 sum_good c(e),
A_bad=4 sum_(all regular nongood pairs) |c(e)|, and B_K is the actual
weighted connected centered sum at sizes3..K with compatible nullity<=3L/2.
The finite family defining R_K is EXACTLY the actual subsets I of G with
rho(I)<=3L/2, I nonretained and |I|<=K. The original source's added terms
B/N and a_N^2 are absorbed by the proved uniform N^epsilon slack; the final
rate is therefore stated in the stronger unit-power form without those
additional nonnegative terms.

FinitePolymerRemainder proves an exact finite subset-generator remainder:
remove the empty component collection and exactly one distinguished good
component BEFORE the exponential majorant. Actual union-recoverable
component collections inject into the remaining powerset, so arbitrary
nonnegative component activities have bound exp(sum_all)-1-sum_good.
The exponential Taylor remainder is proved separately, with its explicit
quadratic budget. No independence of canonical components as random
choices, partition count heuristic, or target remainder is assumed.

CanonicalComponentWeights proves actual canonical blocks pairwise disjoint,
their cardinalities sum to |I|, and the EXACT weighted factorization
u^|I|*|c(I)|=product_C(u^|C|*|c(C)|). ActualComponentRemainder handles zero
coefficients by an exact finite filter. Nonzero coefficients have no
singleton canonical part. Every remaining part is connected, has at least
two sites, and inherits its actual nullity cap by monotonicity. Thus the
component remainder includes affine incompatibility and zero marginals;
no cancelling centered expression is replaced by a joint probability.

CenteredSourcePairBound proves 0<=c(e) and |c(e)|<=q(e) for every actual
positive-joint source pair, from the exact heterogeneous joint rank formula
and the pair covariance identity. NonretainedPositiveMass.pointwise_bound
uses the exact inverse centering expansion and separates the empty term,
source-pair terms and residual terms. Source pairs remain distinguished.
For a nonretained I and a source e subset I, the complement I minus e is
PROVED to fail directness after compression; otherwise I would be retained.
RestrictedSeedComplements.fiber_bound therefore charges that source term
to its actual source-relative independent deficit. No factorization of a
failed extension's arithmetic joint probability is assumed.

SeedComplementSum bounds the sum of EVERY contained residual seed, with
its own nonnegative centered activity and independently weighted free
complement. The exact complement map is injective in each source fiber;
its full finite generator is bounded by exp(sum_x u*p_x). Independent
nonretained terms belong to the actual ordinary independent deficit.
NonretainedPositiveMass.finite_bound combines these comparisons with the
nonlinear actual canonical-component remainder on ANY finite actual ground
G, with exact heterogeneous marginals, ANY fixed u>=0 and ANY size cap K.
Source pairs only need positive actual joint probability and membership
in G.powersetCard2. No equal-marginal assumption, regularity premise or
linear size restriction is used in this finite theorem.

RetainedBoundaryPositiveMass.finite_bound specializes this stronger finite
lemma to the actual regular ground, goodEdges and u=2. Exact marginal
identities identify F and Gdef with firstMass and secondMass; the exact
pair split identifies A_good+A_bad. It proves the source finite inequality
for EVERY K, even when4K>L. The linear restriction is needed only by the
arithmetic rate estimates, not by the finite probability/combinatorics.
Finding P1-MATH-0145 records this separation and heterogeneous extension.

RetainedBadPairActivityUnderInputs keeps every nongood centered pair,
including incompatible sources. Direct nongood pairs have zero coefficient;
the actual dependent ones lie in the height-five tail or finite exceptional
sector at Q=4. Their rates4/5 and1 give A_bad rate4/5. The only input is the
existing finite pair bundle at cap sizeCap(epsilon/128).
RetainedComponentActivityUnderInputs supplies ONE common threshold over
ALL4K<=L: A_bad has rate4/5, B_K rate1, A_good+A_bad rate2/3. B_K uses the
completed literal linear connected theorem at t=4, eta=3/2 and weight2;
the whole pair rate uses the existing fixed-cap pair bundle. These are
proved constituent estimates, not desired-bound premises.

PositiveBoundaryMassUnderInputs uses the fixed internal margin
delta=min(epsilon/4,1/12), selected before N. The total component activity
is at most2*N^(-7/12), hence eventually at most1. Its squared exponential
remainder costs N^(-7/6), while A_bad supplies rate4/5 and B_K rate1.
The actual mean is bounded uniformly; the already completed independent
deficits have stronger rates1 and7/6. A final fixed-factor absorption gives
the literal4/5 rate after one threshold, uniformly in K and L.
The final Hypotheses are a finite union of the SAME three previously
recorded geometric properties: three coarse bundles at margins delta/128,
delta/512, delta/128; their pair caps sizeCap(delta/524288) and
sizeCap(delta/1024); the whole-pair cap sizeCap(1/100); and the nongood-pair
cap sizeCap(delta/128). No BCN or new unproved property is introduced.

This checkpoint adds10 modules,27 theorems,10 definitions and2 finite
parameter structures. Coverage is87/167 unconditional and29 conditional,
with145 confirmed mathematical improvements. The complete-law quadratic
approximation still requires combining this result with the stopped
identity, large-boundary tail and reference conversion; no such completion
is claimed here. The sharp4/3 complete-law rate and T15.1 separated clauses
remain open. No original manuscript bytes, Paper C port, dependency download,
hidden axiom or Palomar registration is added.

Verified under Lean v4.36.0-rc2: full build passed (13663 jobs); direct axiom audit passed for 10574 declarations using only propext, Classical.choice and Quot.sound; all 8972 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 12.53 GiB.


## Complete first quadratic approximation, companion T17.5

Companion T17.5 is COMPLETE CONDITIONALLY, with BOTH original-law quadratic
approximations in ordinary singleton l1 distance. For every C and epsilon>0,
the finite geometric parameters are chosen first; given their explicit
ordinary hypotheses there is ONE threshold before all N and all critical L:

  distance(Law Z_N, Q(mu_N,alpha_N)) <= N^(-4/5+epsilon),
  distance(Law Z_N, Q(N*2^(-L),alpha_N)) <= N^(-4/5+epsilon).

Law Z_N is the actual normalized pushforward of the original infinite
prime-sign count. alpha_N is its exact second factorial cumulant in BOTH
references. Q is the already constructed actual signed Poisson--Charlier
measure, with its literal singleton coefficients. The new signed atomic
distance is the convergent sum of absolute singleton differences; for two
probability measures it is exactly twice actual total variation. No
probability interpretation of a retained polynomial is assumed.

RetainedStoppedLaw transports the exact finite stopped identity to the
actual original regular-count law using a cutoff containing all windows.
Its boundary is split by actual cardinality into the exact low-nullity
nonretained mass and the large-boundary mass. The finite comparison needs
only N>=2,L>=7, with no arithmetic rate premise. Adding the two actual
independent deficits gives the actual binomial pair reference. The cutoff
chosen by BoundaryCutoff satisfies4K<=L eventually. The completed T17.3
bound has rate4/5, the improved unconditional large-boundary tail has
rate5/3, and the two independent deficits have stronger rates1 and7/6.
Their proved combination yields the original regular law's rate4/5 to
the binomial pair reference.

RetainedBetaCovarianceUnderInputs proves the finite parameter identity
and estimate before taking rates: beta minus the covariance of ALL actual
regular pairs is bounded by the independent product mass of good pairs
plus A_bad/4. The good-pair independent mass has unconditional rate1 via
the literal private2:3 and3:4 channels. All nongood pairs, including
incompatible ones, are kept in A_bad, whose established rate is4/5.
PoissonCharlierConversion then converts the actual binomial reference to
the quadratic reference at the exact regular mean and cumulant. Its
analytic error has size N^-2+|C2|/N; unconditional subpower absolute pair
activity makes this error smaller than the requested4/5 budget. The
quadratic coefficient retains the diagonal subtraction -n*p^2.

RegularSecondCumulantRestoration proves UNCONDITIONALLY that removing the
irregular windows changes the actual second factorial cumulant by at most
N^(-1+epsilon). A finite identity identifies the removed pairs with the
actual edges touching the removed ground, and bounds the correction by
twice their absolute centered activity plus the marginal diagonal.
IrregularPairActivity already bounds the first term with rate1, and the
actual marginal cap gives diagonal O_C(1/N). No bounded higher-moment
premise, BCN premise or geometric input occurs in this theorem. This
replaces the earlier bounded-moment route for this particular transfer;
other higher-order moment transfers are not declared unconditional.
Finding P1-MATH-0146 records the improvement.

RegularQuadraticReferenceRestoration combines this unconditional cumulant
transfer with the exact mean gap, the proved nominal mean bias and the
actual original-law coupling. Its generic signed-reference parameter
bound uses the existing Poisson parameter stability theorem. The actual
cumulant has an unconditional subpower envelope. Choosing internal
margins before N proves that law restoration PLUS reference restoration
has rate1, for BOTH the full actual mean and the nominal mean. Thus the
last step of T17.5 introduces no extra arithmetic input and preserves the
full actual alpha_N in the nominal reference.

The only unproved inputs in T17.5 are a finite union of the SAME three
recorded geometric counting properties: normalized-curve uniformity,
ordinary surface cover and chosen-source surface cover. Parameters consist
of the existing retained-component bundle and finite-pair bundle. At
internal margin d=epsilon/2, the first is used at min(d/24,1/12), and the
second at sizeCap(d/768). Their definitions expose the further finite
constituent margins. No desired law bound, BCN bound or moment bound is
an input. All thresholds precede every critical length; no limiting mean
or phase is fixed.

This checkpoint adds7 modules,25 theorems,1 definition and2 finite parameter
structures. Coverage is87/167 unconditional and30 conditional, with146
confirmed mathematical improvements. Main3.1 keeps its proved scope and
gains the unconditional second-cumulant restoration; main1.1 gains the
conditional4/5 quadratic approximation and stays in progress because its
optimal4/3 rate is still open. No source bytes, dependencies, Paper C port,
new hidden axiom or Palomar registration are added.

Verified under Lean v4.36.0-rc2: full build passed (13677 jobs); direct axiom audit passed for 10599 declarations using only propext, Classical.choice and Quot.sound; all 9000 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 12.49 GiB.


## Exact finite all-pair reconstruction toward main15.13

Main15.13 is now IN PROGRESS with its unconditional exact finite
reconstruction and unconditional large-boundary tail. Its complete
implication from the254 fixed connected-activity estimates is NOT yet
claimed. This checkpoint does not add a completed numbered result.

The literal all-pair class D2 on ANY finite actual ground G is constructed:
I is retained when its original square-class spaces are direct, or its
nullity equals that of one contained pair. Every pair of G is allowed,
including incompatible pairs and pairs with zero covariance. Heredity,
empty-set membership and retention of every pair are proved. For a
positive dyadic ground, every first excluded prefix has positive nullity
at most2L, and every subfamily has compatible nullity at most2L.
This is the full2L boundary, not the smaller good-pair boundary from T17.5.

UnrestrictedRetainedExpansion proves the exact inverse-centering expansion
on this class:

  q(I) = product_I p_x + sum_(e subset I, |e|=2) c(e)*product_(I minus e) p_x.

No positivity or compatibility premise is imposed. If a marginal is zero,
the actual centered coefficient vanishes by the already proved zero-mass
argument. Otherwise the full-support relation criterion proves that all
centered coefficients of size at least3 vanish on a retained family.
A primitive original family has c(I)=q(I)-product_I p_x, including the
incompatible case q(I)=0, and product_I p_x<=|c(I)|. Canonical nullity
additivity separately proves that every primitive family is connected;
its compatible nullity is at mostL on the positive dyadic ground.

AllPairPolynomialExpansion proves an exact finite commutative-ring
identity, retaining EVERY signed pair weight. Specialization identifies
the all-pair reference with the full heterogeneous Bernoulli product plus
its signed covariance corrections. SecondOrderRetainedReference proves
that its difference from the actual D2 retained polynomial is precisely
the negative discarded sum of the independent and signed pair terms.
In particular, no incompatible covariance is replaced by a joint event
probability and no equal-marginal reduction is used.

SecondOrderIndependentDeficit charges the independent mass of discarded
families to primitive sources of size at least3 and failed extensions of
a contained pair. For the latter, nonretention itself proves failure of
directness after compression. The exact complement map is injective in
every source fiber. Arbitrary u>=0, arbitrary finite source ground and all
cardinalities are covered; the primitive independent weight is bounded by
its actual centered activity even for incompatible systems.
SecondOrderPositiveMass removes the empty coefficient and the ENTIRE
one-pair contribution before applying the actual canonical-component
generator. The resulting finite probability bound holds for EVERY K.

SecondOrderStoppedLaw.finite_bound is an unconditional bound for the
actual ORIGINAL normalized count law, at any positive dyadic ground,
L>0 and arbitrary K. Write A=sum_pairs 4|c(e)|, T=sum_(connected C,
3<=|C|<=K,compatible-nullity<=2L) 2^|C|*|c(C)|, P=sum_(primitive D,
|D|>=3)2^|D|*|c(D)|, D=the literal all-pair failed-extension deficit
at weight2, and M=sum_x2p_x. Then its exact checked bound is

  distance(Law Z_G, embed B2) <=
    2 exp(M)*P +16 D + exp(M)*(exp(A+T)-1-A) +largeBoundaryMass.

All quantities on the right are explicitly defined finite actual sums.
The original law is transported through an actual containing finite
cylinder and the exact stopped expansion, whose suffix remains positive.
No eventwise polynomial is treated as a probability law.

SecondOrderBoundaryCutoff evaluates the already defined least cutoff at
N^2. It is PROVED to be o(log N), and the log-budget tail is then N^-6.
The literal2L boundary costs O_C(N^2), giving the unconditional final
large-boundary bound2^(2C)*N^-4, uniformly for all G in the dyadic block.
All irregular windows, exact heterogeneous marginals, zero masses and
incompatible systems are retained. No growing-order moment premise is
used for this tail.

This checkpoint adds9 modules,36 theorems and10 definitions. Coverage
remains87/167 unconditional and30 conditional; confirmed mathematical
improvements remain146. These are exact proof constructions and do not
receive a new correction identifier. The next step is to insert the
source254 fixed connected-activity hypotheses, combine the proved tails,
pair activity and pair deficits, and perform the existing sharp analytic
conversion. Main15.13 stays in progress until that implication is checked.
No dependency download, source-byte change, Paper C port, hidden axiom
or Palomar registration is introduced.

Verified under Lean v4.36.0-rc2: full build passed (13695 jobs); direct axiom audit passed for 10635 declarations using only propext, Classical.choice and Quot.sound; all 9046 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 12.44 GiB.


## Complete finite transfer to the full law, main15.13

Main15.13 is now COMPLETE CONDITIONALLY as the literal theorem stated in
the source: for1<beta<=4/3, the254 fixed connected-activity estimates at
orders3 through256 imply the complete original-law quadratic estimate
with rate N^(-beta+epsilon). The same three previously recorded geometric
counting properties remain explicit ordinary arguments for the already
proved all-pair deficit, pair activity and connected tail. No new
geometric counting property is introduced.

The SOURCE FIXED-ORDER ASSUMPTION is explicit and has not been discharged:
FiniteConnectedActivity254.Hypothesis C beta quantifies ONLY r=3,...,256.
For every such r and every positive accuracy it supplies a nonnegative
constant A_r and a threshold before all critical N,L, bounding the sum
of |c(I)| over ALL actual connected r-site families with compatible
nullity<=2L by A_r*N^(-beta+accuracy). The constants may depend on r,C
and accuracy, exactly as in the printed big-O hypothesis. It assumes
neither the desired law bound nor a growing-order activity bound.
This completion proves the stated implication; it is NOT recorded as a
proof of those254 activity estimates, main15.10, main15.14 or main1.1.

FiniteConnectedActivity254.uniform_weighted chooses the254 constants
and thresholds before N using a finite index type. Exact cardinality
filters cover every family of size3..256, and finite fixed weights are
absorbed with a smaller accuracy. There is then ONE threshold for the
entire finite range. PrimitiveConnectedGeometry proves that primitive
original families are connected and have compatible nullity<=L, so the
same hypotheses control primitive sizes3..256. The already proved
unconditional primitive tail supplies all larger sizes with power7/5.
The complete primitive sum consequently has rate beta.

FiniteConnectedClosureUnderInputs combines the exact small-size estimate
with ConnectedTailUnderInputs at the literal cutoff from
SecondOrderBoundaryCutoff. The latter cutoff is proved o(log N). The
connected tail at sizesSTRICTLY GREATER THAN256 has power83/60, which is
strictly stronger than4/3. Every actual connected family of size3..K
and compatible nullity<=2L is retained, including incompatible systems.
Both the complete connected sum and all-cardinality primitive sum have
rate beta after one threshold, uniformly over every G in the full dyadic
ground. No unproved estimate at sizes>256 is added to the hypothesis.

The previous unconditional finite reconstruction theorem remains the
probabilistic mechanism. D2 contains direct original families and families
with exactly the nullity of a contained pair; ALL original pairs are
allowed. Its boundary has nullity<=2L. On D2, inverse centering is exactly
q(I)=product_I p_x+sum_pairs c(e)*product_complement p_x. The retained
polynomial differs from the full heterogeneous Bernoulli-plus-signed-pair
reference by the explicit discarded independent and pair terms. Failed
pair complements are proved non-direct after source compression. The
finite bound uses actual primitive centered mass, the actual all-pair
extension deficit, and exp(A2+T)-1-A2, with the whole linear pair activity
subtracted BEFORE the absolute component estimate. It holds for every K
and exact heterogeneous marginals, including zeros and incompatibility.

FiniteCompleteLawTransferUnderInputs uses a fixed internal accuracy
delta=min(epsilon/8,1/24). Absolute pair activity has rate2/3, the complete
connected remainder has rate beta>1, the all-pair independent deficit has
rate3/2, and the actual large-boundary mass has unconditional rate4.
The total component activity x is at most5*N^(-2/3+delta), hence eventually
at most1. The proved exponential remainder costs T+x^2*exp(x)/2. Its
squared pair term has rate4/3, so beta<=4/3 is exactly sufficient.
A uniformly bounded actual mean controls all free complements. Finally
the already proved signed heterogeneous Poisson--Charlier conversion
has rate5/3 and uses the EXACT actual mean and second factorial cumulant,
including the marginal diagonal. Fixed constants are absorbed before
taking the final threshold.

Parameters are a finite connected-tail bundle, a finite all-pair-deficit
bundle, and two finite-pair bundles for activity and conversion. At the
chosen delta, connected hypotheses use coarse margin delta/128 and
pair caps sizeCap(delta/32768), sizeCap(delta/1048576). The all-pair-deficit
hypotheses use caps sizeCap(delta/2048), sizeCap(delta/65536). Pair activity
and conversion use sizeCap(1/100). The underlying bundle definitions
expose every constituent ordinary surface cover, chosen-source surface
cover and normalized-curve bound. No BCN or bounded-moment assumption
occurs. All parameters, constants and fixed orders precede N; the final
threshold precedes ALL critical lengths and ALL dyadic subgrounds.

article_15_13 specializes the stronger subground theorem to the original
full count law. The source-count law is an actual normalized pushforward,
and the reference is the actual signed Poisson--Charlier measure; distance
is the convergent ordinary sum of absolute singleton differences. The
finite suffix count remains an actual positive kernel, never a freely
expanded signed approximation to a probability.

This completion adds3 modules,5 theorems,2 definitions and4 finite
parameter structures. Coverage is87/167 unconditional and31 conditional;
confirmed mathematical improvements remain146. This is completion of
the source implication and introduces no new correction identifier.
The optimal4/3 activity inputs and main15.14 reconstruction still require
their own proofs. No dependency download, original source-byte change,
Paper C port, hidden axiom or Palomar registration is introduced.

Verified under Lean v4.36.0-rc2: full build passed (13701 jobs); direct axiom audit passed for 10640 declarations using only propext, Classical.choice and Quot.sound; all 9057 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 12.42 GiB.


## Complete modified moments and pair leakage, companion T22.6

Companion T22.6 is COMPLETE CONDITIONALLY, including its exact modified
binomial-moment identity, nonnegativity of all four deficits, the zero
pair terms at order1, and BOTH weighted estimates. Let n=|regularStarts|,
p=2^-L and beta=sum_good q(e). With the literal actual modified count and
the actual exceptional event E'=nonretention, for every r>=1:

  E choose(modified Z,r) = choose(n,r)*p^r -F_r -L'_r
    +beta*choose(n-2,r-2)*p^(r-2) -G_r -H_r,

where the last three terms are zero for r=1. F_r and G_r are exactly the
previous cardinality coefficients; L'_r and H_r are the actual Bochner
expectations, restricted to E', of the direct and compressed-pair subset
counts. All four are proved nonnegative. The finite identity is
UNCONDITIONAL for N>=2,L>0 and EVERY r>=1, with no upper order restriction.

RetainedSubsetCounts constructs the literal deterministic direct and
compressed-family counts. On ANY retained configuration their sum is
choose(|A|,r), by the already proved disjoint direct/pair decomposition.
Every source pair remains distinguished. RetainedPairCountSource.formula
identifies the pair count EXACTLY with sum_e 1_(e subset A) times the
number of U in the source Gamma_e(r-2) contained in A minus e. Thus it is
the printed J_e times admissible-complement count, even on the bad event;
it is not a replacement random variable having the same mean.

SelectedSubsetCounts proves the finite activation/expectation identity
for any prescribed subset class. ActiveSetCylinder transports EVERY
observable and event of the actual active set through a finite cylinder
containing all original windows. These identities give the exact direct
and pair means, including the source Gamma counts, heterogeneous actual
joint events and affine compatibility. The regular marginal identity
then yields the printed nominal powers, with F_r and G_r explicitly
subtracted. The modified count is literally zero on nonretention.
Integrating its pointwise subset-count decomposition gives the source
identity, including both exceptional-event leakages. No moment transfer
or probability interpretation of a retained polynomial is assumed.

The source weighted G estimate has the stronger UNCONDITIONAL rate7/6:

  sum_(r>=0) 2^r*G_r <= N^(-7/6+epsilon).

The exact finite cardinality grouping identifies this sum with the
already proved independent secondMass. Terms at r<2 and r>n vanish,
so the displayed infinite series is literally the finite source sum.
The same convention applies to H_r: its small and large terms vanish,
all terms are nonnegative, and the ordinary real series equals its
finite support sum for every N,L.

ExceptionalEventHolder proves the actual finite eighth-moment Holder
inequality. ActiveSetExceptionalMoment then bounds the contribution
on nonretention of ANY nonnegative active-set observable f(A)<=|A|^j by

  (E Z_G^(8j))^(1/8) * P(E')^(7/8).

The completed exceptional-event theorem at the FIXED margin1/120 gives
P(E')<=N^(-4/5+1/120). The previously proved UNCONDITIONAL subpower
moment bound gives E Z_G^(8j)<=N^(1/120) for each fixed j. Thus the
exceptional contribution is at most N^(-83/120). Its threshold is chosen
before all critical L, all dyadic subgrounds G, and EVERY f satisfying
the pointwise bound. The SAME finite exceptional-event input bundle is
chosen BEFORE ALL fixed degrees j. No uniformly bounded higher moments,
BCN premise or degree-dependent geometric property is needed.

For the actual pair count, a finite combinatorial estimate gives
P_r(A)<=|A|^(r+2). Therefore the same single input bundle proves, for
EVERY fixed r, H_r<=N^(-83/120). The exponent83/120 exceeds2/3 by1/40;
it is sufficient for the requested little-o. P1-MATH-0147 records this
weaker-moment route and its stronger quantifier/input scope, not an
improvement over the source's fixed-order numerical exponent7/10.

RetainedPairMomentGenerator proves the exact shifted-binomial generator
bound for the UNRESTRICTED positive pair moments:

  sum_(r=0..n) u^r E P_r <= u^2*beta*(1+u*p)^(n-2)
    <=u^2*beta*exp(u*E Z_regular), for u>=0,n>=2.

Since H_r<=E P_r, it also bounds every exceptional subseries.
RetainedGoodPairScale bounds beta by a constant times the literal nominal
second factorial correction a_N=E(Z_N)_2-(N*2^-L)^2, UNCONDITIONALLY.
It uses the homogeneous principal-channel upper bound and the existing
unconditional positive lower bound a_N>=c_C*L*N^-2/3. Consequently the
ENTIRE4^r-weighted H sum is at most A_C*a_N, without geometric premises.
The actual mean cap and eventual regular cardinality>=2 are discharged.

WeightedLeakageCutoff splits the2^r sum at an arbitrary fixed J. Its
finite part is controlled by the fixed-order rate83/120; the remaining
part is at most2^-J times the4^r generator. Choose J after a positive
tolerance eta, then absorb the finite constant using the gap1/40 and
the proved lower bound for a_N. This yields the full uniform statement:

  for every eta>0, eventually for EVERY critical L,
  sum_(r>=0) 2^r*H_r <= eta*a_N.

The SAME finite geometric bundle was chosen before eta and before every
fixed order. No growing-order moment estimate is assumed or invoked.
ModifiedMomentDecompositionUnderInputs.companion_T22_6 assembles all
source clauses with this quantifier order. Its only unproved inputs are
the SAME three recorded geometric counting properties, through the
existing RetainedExceptionalEventUnderInputs.Hypotheses at1/120.
Every constituent finite cap is exposed in that bundle definition.

This checkpoint adds16 modules,50 theorems and15 definitions. Coverage
is87/167 unconditional and32 conditional, with147 confirmed mathematical
improvements. Main1.1's optimal4/3 bound, main15.10 and main15.14 remain
open; the completed T22.6 does not silently discharge them. No dependency
download, original manuscript-byte change, Paper C port, hidden axiom or
Palomar registration is added.

Verified under Lean v4.36.0-rc2: full build passed (13733 jobs); direct axiom audit passed for 10690 declarations using only propext, Classical.choice and Quot.sound; all 9122 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 12.36 GiB.


## Complete primitive mass at four blocks and all fixed orders, main15.5

Main Proposition15.5 is COMPLETE CONDITIONALLY, including its formerly
open r=4 case. For every fixed r>=4 and positive epsilon, one finite
bundle of the SAME three existing geometric counting properties gives
one threshold before every critical length L, dyadic subground G and
actual primitive subpopulation F of size r. Both source bounds hold:

  mass(F)=sum_I (product_(x in I) actual p_x)*2^rho(I)
    <=N^(-4/3+epsilon),
  mass(F)<=N^(-2r/(r+2)+epsilon).

The SECOND bound now holds on the WHOLE primitive population: the dense
nullity restriction is unnecessary. At r=4 the two exponents coincide.
For every fixed r>=5 the existing stronger UNCONDITIONAL elementary
bound N^(1-r/2+epsilon) already gives both inequalities on the whole
population. The new conditional proof is needed only at r=4. All exact
heterogeneous marginals, including zero marginals and irregular windows,
are retained. No affine compatibility or positive joint-event premise
is imposed, and no fixed-order result is used at a growing order.

For r=4 below rho<L/2, the proved independent primitive mass has power2;
the rank factor costs only N^(1/2+o(1)), giving the UNCONDITIONAL stronger
rate3/2. The dense sector rho>=eta*L, for each fixed eta>0, has power4/3
under the existing two-target geometric inputs. Its four sectors are
literal finite families, and the proof tracks every source set before
using its uniform two-target extension bound.

FixedAnchorDegreeBudget allows any fixed polynomial width prefactor.
FixedOrderAnchorMass counts actual good-anchor CRT covers at FIXED order
r. The assignment cost is N^(t/A+epsilon), instead of the all-order
factorial-series cost N^(2t/A+epsilon). Its heterogeneous independent
mass therefore has exponent -t*beta+t/A. The threshold depends on r;
this does not alter the existing all-cardinality statement. Furthermore
SelectedAnchorRelation needs only the t selected anchors to have large
kernels. It does not require every value of the source window to have
a large kernel. These are explicit improvements recorded by extending
P1-MATH-0073; no new correction identifier is needed.

Choose A=6, beta=9/10 and t=4. The actual moderate certificate sector has
UNCONDITIONAL rank-weight power29/15, stronger than4/3. The actual
saturated pairs have at most N^(1+4/6+epsilon) source choices, by the
already proved literal outgoing-degree theorem. Fixing each such source
pair leaves exactly two dense primitive targets. The restricted
extension theorem gives a uniform cost (K_C/N)^2*N^(-1+epsilon), so the
complete saturated mass has rate4/3.

For the small-kernel sector, the proof uses the already proved enlarged
population Bad of windows having two values with EACH K_(L+1)<=N^(2/3).
Its cardinality is N^(2/3+epsilon). Marking one such source and any other
source gives at most N^(5/3+epsilon) source pairs; the same two-target
estimate gives rate4/3. This enlarged population has sufficient size
control; the more specific product-cap population is unnecessary here.

WindowSquareKernelBound proves the exact finite inequality

  a_Y(v)^2*K_H(v)<=v

for every positive integer v and ALL cutoffs H,Y. It follows by removing
the actual square factor, preserving its full parity vector, and bounding
the actual remaining odd kernel by the quotient. Consequently, outside
Bad, at most ONE value has a_Y(v)^2>N^(2/3), eventually. No smoothness
assumption, pairwise separation or unproved square-part count is used.

RestrictedSupportRank proves a finite binary-code estimate: if every
word has at most d nonzero coordinates outside S, the actual code rank
is at most |S|+d. The physical code projects onto every actual effective
relation. A primitive projects injectively onto each whole block. If
neither a moderate four-anchor certificate nor a saturated pair exists,
every physical relation selects at most three large-kernel coordinates
in each block. Thus EVERY window has at least rho-3 small-kernel
coordinates. Dense rho is eventually at least15, so deleting the one
possible large square part leaves eleven literal distinct small-kernel
values with controlled square parts.

With m=11, A=6, beta=9/10, u=2/3, the completed several-small-kernel
window theorem bounds this actual Rare population by N^(5/6+epsilon).
Any two-source subset of an all-Rare four-window primitive lies in
Rare.powersetCard2, of cardinality at most N^(5/3+epsilon). The SAME
restricted two-target theorem supplies rate4/3 for this last sector.
The four exact sectors cover every dense primitive family. Fixed
constants and smaller margins are absorbed before the final threshold.

RestrictedDensePrimitiveMassUnderInputs proves a reusable, stronger
source-population statement: for any fixed s>=1 and source-population
exponent sigma, actual dense primitive extensions of size s+2 over at
most N^sigma prescribed source sets have rank mass
N^(-1-s+sigma+epsilon). It constructs the parameter bundle from the
proved two-target theorem; it does not assume a desired family mass.
The same bundle, chosen before N,L and all source/subfamily choices,
controls the three source-restricted sectors of the four-block proof.

Only P1-GEO-CHOSEN-SOURCE-SURFACE-COVER,
P1-GEO-ORDINARY-SURFACE-COVER and P1-GEO-NORMALIZED-CURVE-UNIFORM remain
unproved ordinary arguments. No BCN, bounded moments, target primitive
mass or new literature property is assumed. The finite anchor, code,
square and source-cover results are unconditional. This checkpoint adds
13 modules,30 theorems and8 definitions. Coverage is87/167 unconditional
and33 conditional; the existing finding73 is extended and the confirmed
finding count stays147. The sharp triple activity, main15.10 reduction,
main15.14 reconstruction and optimal main1.1 remain open. No dependency
download, Paper C port, original source-byte edit, new axiom or Palomar
registration is introduced.

Verified under Lean v4.36.0-rc2: full build passed (13759 jobs); direct axiom audit passed for 10720 declarations using only propext, Classical.choice and Quot.sound; all 9160 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 12.31 GiB.


## Complete reduction of connected activities to triples, main15.10

Main Proposition15.10 is COMPLETE CONDITIONALLY, including BOTH the
reduction to the actual third absolute activity and the sharp3/2
incompatible remainder. For each fixed R, every positive epsilon has
one finite bundle of the same three geometric properties and one
threshold before all critical lengths, all orders3<=r<=R, all dyadic
subgrounds G and every actual connected subpopulation F of size r:

  sum_(I in F)|c(I)| <= N^epsilon*A3(G)+N^(-4/3+epsilon),
  sum_(I in F,q(I)=0)|c(I)| <=N^(-3/2+epsilon),

where A3(G)=sum_(D subset G,|D|=3)|c(D)| is the literal actual third
absolute centered activity. article_15_10 specializes the stronger
bounded-range result to each fixed r>=4 and the entire connected
population. It assumes no desired bound for A3, no count-law estimate
and no sharp fixed-order connected activity input. Exact heterogeneous
marginals, zero-marginal sites and every affine incompatibility remain
in the original model throughout.

IncompatibleHigherDeficit first separates all actual PAIR sources from
the proper-source expansion. Singleton centered coefficients vanish
exactly. Every pair contribution is charged to the already proved
all-cardinality pair deficit, of rate3/2. Only proper sources of sizes
at least3 remain. FixedActivityInputBundle supplies their complete
absolute activity at the already proved COARSE rate1, using the existing
fixed-moment geometric bundle. The independent non-direct complement
cost has UNCONDITIONAL rate1/2 uniformly over bounded source sizes.
Multiplication gives rate3/2 for ALL remaining sources. The independent
connected-family term is at most N^(-r/2+epsilon), sufficient already
at r=3. One finite cardinality split and fixed-constant absorption give
one threshold for all3<=r<=R.

This proves the source's sharp incompatible remainder WITHOUT the
optimal arithmetic triple exponent41/30 and without an induction on
the new sharp connected rate. The printed proof invokes that stronger
triple input. The weaker coarse full-activity theorem suffices once the
pair deficit is separated before applying the half-power complement
bound. P1-MATH-0148 records this reduction of mathematical prerequisites.
No target sharp estimate is assumed, directly or through an interface.
The coarse activity proof uses earlier independent modules and does
not depend on this new sharp incompatible theorem.

VariableConnectedSeedCatalog proves the same exhaustive actual seed
cover with an arbitrary fixed small-intersection threshold eta, rather
than the previous hardcoded1/12. The catalog contains primitive seeds,
connected triples, low-intersection two-pair seeds, dense pair crossings
and minimal direct-crossing seeds. The exact finite cover precedes all
probability and asymptotic estimates, and includes all connected
original-window families, whether compatible or not.

SharpConnectedSeedCatalogUnderInputs chooses eta=epsilon/8 BEFORE N.
Primitive seeds of size>=4 use the newly completed main15.5 rate4/3;
primitive triples are included in the positive connected triple mass.
That positive triple mass is already bounded by A3 with coefficient1
and an error of rate3/2. Dense pair crossings and every fixed minimal
direct crossing have rate5/3. Low-intersection two-pair seeds have
rate4/3 minus eta; this fixed loss is absorbed in the requested margin.
The finite primitive/direct size ranges are assembled before choosing
N. The complete seed mass is bounded by N^epsilon*A3+N^(-4/3+epsilon).
No sharper pair-target rank estimate or separated compressed all-order
hypothesis is added.

VariableSeedMassPropagation retains actual positive joint moments and
extends every seed of bounded size to the prescribed fixed target size.
Its only constant is the actual target factorial, and its power loss
can be any fixed positive margin. CompatibleTripleJointBound bounds
|c(I)| by2^|I|*q(I) only on the positive joint-event sector. Both finite
constants are absorbed with smaller fixed margins. The remaining
zero-joint-event sector uses the NEW independent3/2 proof, instead of
applying a positive joint bound to an incompatible event. This gives
the complete actual centered-activity reduction, with no compatibility
substitution or signed retained polynomial used as a probability.

The compatible parameter bundle at margin z contains finitely many
primitive and direct two-target bundles, one triple pair bundle at
sizeCap(z/8192), a low-pair bundle at sizeCap(z/32768), and dense/direct
pair bundles at sizeCap(z/16384). SharpIncompatibleActivityUnderInputs
at margin z contains the existing fixed-moment bundle, plus the exact
finite all-pair deficit initial and entry bundles at sizeCap(z/8192)
and sizeCap(z/262144). The final combined theorem calls these compatible
and incompatible bundles at epsilon/8 and epsilon/2 respectively.
Every constituent hypothesis is one of the SAME chosen-source surface
cover, ordinary surface cover and normalized-curve count properties.
They remain ordinary explicit arguments, never global axioms.

This checkpoint adds8 modules,10 theorems,2 definitions and6 finite
parameter structures. Main15.10 changes from in_progress to conditional.
Coverage is87/167 unconditional and34 conditional; confirmed improvements
increase147 to148. The optimal arithmetic triple bound, main15.14's
optimal law consequence, main1.1 and Palomar remain open. No dependency
download, Paper C port, original source-byte change, new literature
property or hidden axiom is introduced.

Verified under Lean v4.36.0-rc2: full build passed (13775 jobs); direct axiom audit passed for 10730 declarations using only propext, Classical.choice and Quot.sound; all 9178 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 12.26 GiB.


## Symbolic law reconstruction and stronger first quadratic rate

The full SYMBOLIC estimate of main15.14 is proved for the actual original
count law, exact mean and actual second factorial cumulant:

  ||Law(Z_G)-Q(mu_G,kappa2_G)||_1
    <=N^epsilon*A3(G)+N^(-4/3+epsilon).

Here G is ANY subset of the dyadic block and A3(G) is the actual sum of
absolute original centered coefficients on G.powersetCard3. One finite
bundle of the SAME three geometric properties and one threshold precede
all critical lengths and all subgrounds. The source specialization
article_15_14_symbolic uses the entire original dyadic block. No desired
law approximation, sharper triple activity, finite connected-rate
hypothesis or uniformly bounded growing moment is assumed.

Main15.14 changes from not_started to IN_PROGRESS, not conditional or
proved: its final optimal4/3 law consequence still needs the unproved
sharp arithmetic triple estimate41/30 (or a sufficient substitute).
The complete symbolic inequality does not establish that numerical
optimal rate by itself. Main1.1 also remains in_progress.

TripleControlledFixedActivity uses the newly completed main15.10 at
ALL orders3..256, with one finite cardinality split. It sums arbitrary
fixed nonnegative weights while keeping A3(G) symbolic. Fixed constants
are absorbed using smaller margins. No connected-activity rate is
supplied as an external input. The exact chosen geometric parameters
precede N and every actual subpopulation.

TripleActivityClosureUnderInputs closes BOTH the entire connected
remainder up to SecondOrderBoundaryCutoff and the all-cardinality
primitive deficit sum, each with the same symbolic bound. Bounded
primitive families are genuinely connected, so the finite theorem
applies to them. The existing UNCONDITIONAL primitive tail has rate7/5.
The actual connected tail at sizes STRICTLY>256 has rate83/60 under
its existing finite geometric bundle. Both exceed4/3. The literal
cutoff is already proved o(log N); no bounded-order constant is used
at that growing order. One finite bundle and common threshold handle
both complete sums and every dyadic subground.

TripleActivityLawReconstructionUnderInputs then applies the already
proved unconditional finite second-order stopping inequality to the
original normalized count pushforward. D2 retains all pairs, with every
signed pair coefficient and exact heterogeneous marginal, including
zeros and all affine incompatible cases. Its suffix kernel remains a
positive actual probability kernel. Its comparison reference is a
signed measure; no retained polynomial is declared to be a probability.

Write a for the complete weighted pair activity and b for the higher
component activity. The nonlinear error is bounded BEFORE the pair
term is restored:

  exp(a+b)-1-a <= b+(a+b)^2*exp(a+b)/2.

The linear b and the primitive deficit stay symbolic. Only the earlier
coarse full activity A3(G)<=N^(-1+delta) is used to show that a+b<=1 and
that its square costs N^(-4/3+4delta). In fact a<=4V, b<=2V for
V=N^(-2/3+2delta); thus (a+b)^2<=36V^2. There is no loss of the linear
A3 term through an unjustified optimal numerical substitution.
The complete pair deficit has rate3/2, the large actual stopped boundary
has unconditional rate4, and the exact heterogeneous signed-reference
conversion has rate5/3. All suffice at this precision.

The internal accuracy is delta=min(epsilon/16,1/48), fixed before N.
The final parameter bundle consists of the symbolic connected/primitive
closure, the earlier coarse order3 activity bundle, the finite full
pair-deficit initial and entry bundles at sizeCap(delta/2048) and
sizeCap(delta/65536), and pair/conversion bundles at sizeCap(1/100).
The coarse order3 bundle is used at4delta. Each underlying condition is
one of P1-GEO-CHOSEN-SOURCE-SURFACE-COVER,
P1-GEO-ORDINARY-SURFACE-COVER or P1-GEO-NORMALIZED-CURVE-UNIFORM.
They remain ordinary explicit arguments, not global axioms. No BCN,
sharp A3 bound or target law estimate is hidden in the bundle.

The same uniform_estimates theorem returns both the proved coarse A3
bound and the symbolic reconstruction after the SAME threshold. This
has a new numerical consequence. QuadraticRateOneUnderInputs.uniform_exact
chooses smaller fixed margins and proves, on every original subground,

  ||Law(Z_G)-Q(mu_G,kappa2_G)||_1 <=N^(-1+epsilon).

Applying this to the original regular subground and then using the
already proved UNCONDITIONAL law/mean/second-cumulant restoration gives
BOTH full-model approximations, with exact or nominal mean and the SAME
full actual second factorial cumulant, at rate1. This strengthens the
printed rate4/5 in companionT17.5. P1-MATH-0149 records the improvement.
No new optimal triple estimate is needed for this stronger first
approximation, and neither the optimal4/3 remainder nor its lower bound
is asserted. The old4/5 declarations remain valid.

This checkpoint adds4 modules,7 theorems and4 parameter structures.
Main15.14 is in_progress; companionT17.5 remains conditional with the
stronger rate1, and main1.1 gains the same checked numerical bound.
Coverage stays87/167 unconditional and34 conditional; confirmed
improvements increase148 to149. No dependency download, Paper C port,
original source-byte edit, new literature input, hidden axiom or Palomar
registration is introduced.

Verified under Lean v4.36.0-rc2: full build passed (13783 jobs); direct axiom audit passed for 10737 declarations using only propext, Classical.choice and Quot.sound; all 9189 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 12.23 GiB.


## Complete fourth-cumulant identities with a stronger first error

Main Lemma16.1 is complete conditionally for the actual full original
count, including all three literal identities and K4positive>=0. In fact
its first error has the stronger power5/3:

  |kappa4-24*K4| <=N^(-5/3+epsilon),
  |K4-K4positive| <=N^(-3/2+epsilon),
  |kappa4+3*alpha^2-(3*alpha^2+24*K4positive)| <=N^(-3/2+epsilon).

Here alpha is the actual second factorial cumulant, K4 sums the actual
original centered coefficients over all connected quadruples of the full
dyadic block, and K4positive retains precisely those with positive actual
joint probability. Every heterogeneous marginal, repeated index, zero
marginal and incompatible affine configuration is retained. One finite
bundle of the SAME three geometric properties and one threshold precede
all critical lengths. No optimal triple estimate, target cumulant bound,
abstract non-direct-cost assumption or BCN premise is used.

The key new unconditional estimate is a GLOBAL count of two actual
compressed pairs, rather than a fixed-source exceptional-target count.
For fixed channels (a,b),(c,d), with positive ordered entries, both
actual unit relations and a nonzero intersection between their actual
effective spaces, all literal ordered source quadruples have cardinality
at most N^(1+epsilon), after all four offsets have been summed.
Each first source pair is uniquely recovered from its compressed anchor
when its two offsets are fixed. The host key consists of the two anchors.
Its two compressed blocks are actual unions of dilated original window
values, of height between N/2 and 3(b+d)N, and width (b+d)(L+1).
Their even square-class spaces equal the sums of the two original spaces.
The existing unconditional dependent-block pair count applies to these
literal blocks, including equal compressed centers. The four offset
patterns cost only a fixed polylogarithmic factor. No branching statement
for a new assumed population is inserted.

For the actual good-good apart products, a finite cover is proved from
unordered pairs of disjoint edges to these source quadruples. Non-direct
nullity is equivalent to a nonzero intersection of the two total spaces,
because the edge vertex sets are disjoint. All finite retained channels
are summed after their parameters have been fixed. Thus their actual
unordered population also has cardinality N^(1+epsilon), uniformly in the
private threshold H. At H=2Q(L+1), each good actual centered coefficient
has size N^(-5/3+epsilon), by the existing private-channel ratio and exact
heterogeneous marginal cap. Their complete product mass consequently has
the stronger UNCONDITIONAL power7/3, replacing the source proof's11/6.

The complement is controlled by an exact nonnegative finite cover. Every
product involving an edge outside the good class is charged to
A2*(Aweak+Aexceptional), with no missing repeated bad edge or implicit
sign assumption. The exact actual pair activity decomposition identifies
the complement weight. Choosing the partition's fixed small parameter
after epsilon and before N gives rate5/3 for the entire literal
nonDirectApartCost. This step uses the existing finite geometric inputs
for the actual pair, weak and exceptional activities; its good-good
part remains unconditional.

Repeated-edge and shared-vertex products have rate5/3 under the same
finite inputs, using the unconditional actual covariance-row bound and
marginal cap. The exact fourth repeated-index remainder has rate2:
its costs are p_*A3, p_*^2 A2 and p_*^3 mu. The already established coarse
FULL third absolute activity of rate1 suffices. The unproved optimal
triple rate41/30 is unnecessary for this lemma. Combining these finite
costs with the exact connected fourth-cumulant identity proves the
stronger first error5/3. Incompatible connected quadruples have rate3/2
by the already completed sharp incompatible activity theorem; its proof
also uses only coarse higher activity. Compatible original coefficients
are nonnegative, yielding the other two source identities.

FourthConnectedCumulantUnderInputs.Hypotheses makes all finite inputs
explicit: coarse order3 activity at epsilon, four sharp-pair bundles at
sizeCap(1/100), and one actual partition bundle at sizeCap(epsilon/2048).
The final Lemma16.1 bundle uses this at epsilon/2 and the existing sharp
incompatible order4 bundle at epsilon/2. These reduce to ordinary
arguments for P1-GEO-CHOSEN-SOURCE-SURFACE-COVER,
P1-GEO-ORDINARY-SURFACE-COVER and P1-GEO-NORMALIZED-CURVE-UNIFORM.
They are not global axioms. The earlier BCN preparatory declarations
remain valid but are no longer needed by the completed source theorem.

P1-MATH-0150 records the stronger global compressed-pair count, the
unconditional good-good cost7/3, the complete apart cost5/3, and the
improved first cumulant error5/3. The second and positive-quartic errors
retain3/2, because the incompatible contribution is controlled at that
rate. Main16.2 and the optimal4/3 law lower bound remain open at this
checkpoint. This does not claim completion of the optimal upper bound,
sharp triple arithmetic, both documents or Palomar preparation.

No original manuscript byte, dependency, external literature input,
Paper C port, new axiom or Palomar registration is introduced. Coverage
is87/167 unconditional and35 conditional; confirmed improvements150.

Verified under Lean v4.36.0-rc2: full build passed (13805 jobs); direct axiom audit passed for 10760 declarations using only propext, Classical.choice and Quot.sound; all 9222 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 12.18 GiB.


## Optimal-power lower inequality for the full exact quadratic reference

The lower inequality displayed in main Theorem16.2 and the optimal
quadratic lower clause of main1.1 are now proved for the actual full
original law and exact actual mean/second factorial cumulant:

  ||Law(Z_N)-Q(mu_N,alpha_N)||_1 >=c*N^(-4/3-epsilon), c>0.

This is the ordinary full singleton l1 distance of the actual original
probability measure and the literal quadratic Poisson signed measure.
No retained finite polynomial, formal coefficient norm, truncated law,
assumed norm comparison or positivity of the reference replaces it.
All original heterogeneous marginals and affine incompatibilities are
retained. One finite bundle of the SAME three geometric properties is
chosen before N and before all critical lengths. The already open optimal
triple activity and optimal upper law rate are NOT inputs to this lower
bound. Main16.2 moves from not_started to IN_PROGRESS: its lower inequality
is complete, but its concluding identification of the optimal power also
refers to the still open optimal upper bound. Main1.1 stays in progress.
Neither row is counted complete at this checkpoint.

PositiveQuarticObstructionUnderInputs uses completed main16.1 at the
FIXED margin1/12 and the unconditional actual alpha lower bound
alpha>=d*L*N^(-2/3). Its error is N^(-17/12), smaller than alpha^2 at
power4/3. After a common threshold, the actual coefficient satisfies

  kappa4+3alpha^2 >=2alpha^2 >=d'*L^2*N^(-4/3).

The compatible connected contribution is nonnegative. This inference
uses only the earlier coarse third activity through main16.1; the
still open41/30 triple estimate is unnecessary.

The fourth Charlier polynomial is literal:

  H4(k;mu)=(k)_4-4mu(k)_3+6mu^2(k)_2-4mu^3 k+mu^4.

Its uniform envelope |H4|<=(1+M)^4(1+k)^4 is proved whenever0<=mu<=M,
without a lower positive mean premise. OriginalLawPolynomialMoments
identifies EVERY actual singleton test sum with the finite observation
expectation and original infinite count integral. In particular the
exact H4 sum is kappa4+3alpha^2, including all repeated-index terms.
FourthCharlierReference proves its sum against Q(mu,alpha) is exactly0
for EVERY mu>=0 and real alpha, using genuine convergent factorial
moment sums, not a formal generating function assertion. General shifted
Poisson factorial sums and the quadratic factorial correction are
proved at every fixed order.

PoissonPolynomialMoments gives a positive summable envelope for the
absolute quadratic signed reference, uniformly over0<=mu<=M and|alpha|<=1.
It compares mass(mu,k) with exp(M)*mass(M,k) and controls both genuine
shifted sequences in the second difference. Every polynomially weighted
absolute series is summable and has a uniform finite bound. The actual
mean is uniformly bounded, and the already proved sharp pair bound
makes the actual |alpha|<=1. The earlier bounded fixed ordinary moments
supply the corresponding actual-law bound.

PolynomialTestTruncation proves a general signed-sequence estimate from
a FIXED higher moment, with all summability discharged. If|f(k)|<=K(1+k)^d,
r>=d and R>=1, then

  |sum a_k f(k)| <=K R^d sum|a_k|
                    +(K/R^(r-d))*sum|a_k|(1+k)^r.

Its proof splits the pointwise envelope at1+k=R, before taking the true
convergent infinite sums. It never applies a bounded-test inequality
directly to an unbounded polynomial. FourthCharlierLawDistance applies
this to the literal difference of the actual-law and quadratic-reference
singleton sequences. The unweighted sum is proved equal to the exact
SignedAtomicDistance.distance of those actual signed measures.

For a prescribed epsilon>0, set delta=epsilon/8 and
r=4+ceil((7/3)/delta). This integer is FIXED before N. At R=N^delta,
the weighted tail has power at least7/3 and is absorbed into half the
positive quartic coefficient. The low part costs R^4=N^(epsilon/2).
Dividing gives a positive constant times N^(-4/3-epsilon/2), hence the
stated lower bound with epsilon. The single moment bundle is used at
accuracy1/2, its pair and alpha bundles at sizeCap(1/100), and the quartic
bundle at1/12. All are finite and reduce to the same three explicit
geometric properties; no uniformly bounded growing-order moment is
assumed, and no target law lower bound occurs among the premises.

This checkpoint adds8 modules of actual polynomial sums, reference
moments, a general truncation inequality and the assembled optimal-power
lower inequality. It introduces no further mathematical improvement ID:
the needed removal of the optimal triple premise is already recorded in
P1-MATH-0150. No original source byte, dependency download, Paper C port,
new literature input, hidden axiom or Palomar registration is introduced.
Coverage remains87/167 unconditional and35 conditional, with150 confirmed
improvements. The optimal numerical upper rate and main15.14 final
numerical consequence remain open.

Verified under Lean v4.36.0-rc2: full build passed (13821 jobs); direct axiom audit passed for 10784 declarations using only propext, Classical.choice and Quot.sound; all 9249 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 12.14 GiB.


## Complete explicit references and fixed-height original-law hierarchies

Main Corollary1.4, Theorem18.1 and Corollary18.3 are complete
conditionally, for the ACTUAL FULL original law and the literal finite
channel coefficients. One finite bundle of the SAME three geometric
properties precedes N and every critical length. No optimal triple41/30,
optimal exact-reference4/3 law bound, target truncation remainder or
homogeneous nonaligned-rank estimate is assumed.

ExplicitQuadraticApproximationUnderInputs.article_1_4 gives the complete
source two-channel reference: its full original-law singleton l1 error
is N^(-4/5+epsilon), the actual signed reference is eventually a probability,
and every singleton has exactly the printed Poisson--Charlier mass.
The coefficient is the literal finite S_23+S_34 expression and its mean
is the nominal N*2^(-L). The proof combines the already completed actual
pair profile with the stronger first quadratic rate1; it does not use
the still open optimal quadratic upper bound. Reference probability
status and its mass formula were already unconditional and are included
in the assembled source theorem after the same threshold.

For EVERY fixed height h>=3, the complete cumulant hierarchy is proved:

  |alpha-coefficient_h| <=N^(-1+1/(h+1)+epsilon),
  |alpha-coefficient_h-heightMass_(h+1)|
       <=N^(-(h+1)/(h+2)+epsilon).

All finite lower-order terms in each exact signed channel polynomial
are retained. Alpha is the actual full second factorial cumulant,
already identified with Var(Z)-E(Z), and heightMass is exactly
lambda^2/N times the full height sum T_(h+1)(L). The source exponent
identity -1+1/(h+2)=-(h+1)/(h+2) is itself checked.

FixedHeightPrivateChannels proves actual reduced-channel uniqueness
from the two exact unit alignments. At4Q^2(L+1)<N the integer determinant
between two distinct reduced slopes cannot vanish on an actual dyadic
source pair. Coprimality then identifies the two channels. Hence their
actual unordered private edge families are pairwise disjoint. Their
union is a literal subset of the actual pair powerset, and its absolute
sum equals the sum over channels with no multiplicity assumption.
An exact sigma/product index bijection identifies the sum of main terms
with the source finite-height coefficient.

The full signed-pair remainder outside that private union is bounded by
the ACTUAL weak plus exceptional activities of the finite pair partition.
This includes all nonaligned, incompatible, locally defective and boundary
pairs. Independent nonzero-cardinality families have zero centered
coefficient, as proved earlier. The fixed-height weak tail is bounded
unconditionally at power1-1/(h+1). The complete exceptional class has
power1 under the recorded geometric inputs, without a homogeneous-rank
substitute on incompatible pairs. Each retained channel's joint main
term, independent correction and sign gap have power1. The diagonal
sum of the exact squared marginals has power1 as well. These facts
assemble the literal coarse cumulant profile. No target profile is
provided as a premise.

FixedHeightQuadraticLawUnderInputs proves both the original-law coarse
approximation and the COMPLETE first-omitted-height signed remainder.
In the latter, the exact signed measure Law(Z)-Q(lambda,coefficient_h)
is compared with (heightMass_(h+1)/2)*Pi_lambda*Delta^2. The remainder is
N^(-(h+1)/(h+2)+epsilon) in the ordinary full singleton l1 metric.
The exact reference-increment and signed-measure translation identities
are checked before applying the metric estimate. The first quadratic
rate1 suffices at every fixed height because (h+1)/(h+2)<1. Neither
optimal4/3 reconstruction nor sharper triple activity is needed.

The actual original-law leading distance equivalent is also proved.
For fixed h,C, ONE finite geometric bundle, chosen at the positive margin
1/(2(h+1)(h+2)), precedes EVERY tolerance tau>0. After its corresponding
common threshold and for ALL critical L, an actual probability witness
Q_h for the literal reference satisfies

  |TV(Law(Z),Q_h)/(phaseMass_(h+1)*norm(Pi_lambda*Delta^2)/4)-1|<=tau.

The phase retains L mod(h+1), the moving nominal mean, and the Poisson
second-difference norm at that same mean. The leading denominator is
proved positive. The smaller actual-law error at height h+1 is compared
with the already established exact gap of adjacent references. A uniform
power separation and the positive full phase lower bound make that
error negligible. The reverse triangle inequality is applied to actual
signed distances; the factor2 between l1 and actual total variation
is retained. A separate quantitative lower bound
c*N^(-1+1/(h+1)), c>0, for the actual full law-to-reference l1 distance,
together with the coarse upper estimates at every positive loss,
proves the claimed optimal power h/(h+1). These are original-law
conclusions, rather than distances only between constructed references.

FixedHeightHierarchyUnderInputs.article_18_1 assembles both literal
remainder statements, actual probability status and the full moving
TV equivalent, with one finite bundle and common threshold. The earlier
phase constants give the source c_b(r), including its positivity.

TwoChannelReferenceUnderInputs specializes the source hierarchy at h=4
and h=5. The two-channel signed remainder has power5/6 and the leading
correction is precisely M5. The exact closed M5 formula, the identity
coefficient5=twoChannelCoefficient+M5 and both finite S_35/S_45 formulas
were already proved and remain literal. The actual-law TV equivalent
at h=4 has the printed coefficient17(r+4)/(1200*2^(r/5)), the moving
lambda^(9/5), the actual norm and L*N^(-4/5). At h=5 it has the moving
height6 phase; its printed c6(r)=(r+5)/(45*2^(r/6)) and lambda exponent11/6
are identified exactly. Thus both the two-channel optimal power4/5 and
the four-channel optimal power5/6 concern their specified original-law
references, with all residues varying after the same threshold.

ExplicitHermiteLawUnderInputs additionally proves the entire explicit
fixed-height Hermite part of main19.1: every fixed h>=3 has original-law
rate h/(h+1) and exactly the same moving TV equivalent as its quadratic
reference. Actual independent-Poisson Hermite probabilities are supplied
by the earlier unconditional construction. The unconditional quadratic/
Hermite error has power4/3 and is negligible on every first omitted
height. Main19.1 nevertheless stays IN_PROGRESS: its exact-parameter
Hermite error4/3 still needs the unproved optimal exact-reference upper
bound. No optimal Hermite lower bound is asserted.

P1-MATH-0151 records the weaker dependency of this whole fixed-height
hierarchy and explicit reference completion: the already proved first
quadratic rate1 plus actual pair-profile remainders suffice. The optimal
triple arithmetic, exact quadratic4/3 upper bound, and the stronger
homogeneous nonaligned main18.2 statement remain open and independent
of this completion. This is not a proof of those missing statements.

The same existing finite geometric properties remain ordinary explicit
arguments: normalized curve count, ordinary surface cover and chosen-
source surface cover. No BCN, new literature input, manuscript byte edit,
dependency download, Paper C port, hidden axiom or Palomar registration
is introduced. Coverage increases from87 unconditional35 conditional
to87 unconditional38 conditional; confirmed improvements151.

Verified under Lean v4.36.0-rc2: full build passed (13837 jobs); direct axiom audit passed for 10816 declarations using only propext, Classical.choice and Quot.sound; all 9288 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 12.09 GiB.


## Complete homogeneous weighted nonaligned pair statement

Main Lemma18.2 is complete conditionally, including its literal
HOMOGENEOUS rank-weight sum and actual covariance consequence:

  sum_(ordered regular separated nonaligned)(2^rho-1)<=N^(1+epsilon),
  sum_(same ordered pairs)|q(x,y)-p_x*p_y|<=N^(-1+epsilon).

The first statement is proved for the actual effective relation nullity,
without any compatibility filter or actual probability weight. A separate
exact regular-rank identity also expresses it with the arithmetic full
source rank deficit pairLoss=2L-rank(S_x+S_y). The literal source population
regularPairs uses both actual regular-start memberships, the strict
integer absolute separation |x-y|>L, and the source nonalignment predicate.
No affine-incompatible or zero-joint-probability pair is discarded.

The proof composes already established arithmetic results, rather than
introducing a new geometric estimate. NonalignedSourceResidualUnderInputs
already bounds the GENUINE positive arithmetic weight2^pairLoss-1 over
ANY actual dyadic nonaligned ordered family, including all local kernels.
It is not a bound merely on compatible probabilities. Effective relative
nullity is at most that full source loss, and equals it on regular starts.
Fixed smaller margins and constant absorption give the source homogeneous
bound after one common threshold. This closes the previously missing
statement/population bridge in the main18.2 ledger row.

PairRankCovarianceBound additionally proves the exact finite inequality
for EVERY actual two-element original family e at positive length:

  |c(e)| <=prod_(x in e)p_x * (2^rho(e)-1).

If any marginal is zero, its actual centered coefficient is zero. If the
joint is positive, the exact affine formula gives equality. If the joint
is zero but both marginals are positive, nullity cannot vanish by exact
direct factorization. Thus2^rho-1>=1 and bounds its negative coefficient.
This handles incompatible pairs explicitly and retains heterogeneous
marginals. No joint compatibility premise is imposed.

In fact uniform_families proves BOTH the homogeneous bound and actual
covariance bound for EVERY finite ordered distinct nonaligned dyadic
family, even without regularity or a separation restriction. It uses the
unconditional actual marginal cap M/N, multiplies the genuine finite
homogeneous sum by (M/N)^2, and proves the exact power cancellation.
Specializing to the original regular separated population gives all
source conclusions. The rank-deficit specialization proves the exact
agreement of both rank conventions on that population.

One finite parameter bundle uses the SAME chosen-source surface,
ordinary two/three-radical surface and normalized-curve properties,
at sizeCap(epsilon/32). Its choice precedes N, every critical L and
EVERY actual finite ordered family. No target rank sum, covariance bound,
BCN premise, new literature theorem or global axiom is supplied.

This is a proof assembly and exact scope extension of the already
recorded P1-MATH-0113 weighted arithmetic source improvement. It does not
create a new improvement identifier. The stronger fixed-height hierarchy
already completed independently remains valid; main18.2 now also has
its own exact homogeneous source statement. The asymmetric compressed
profile T1.10, optimal triple41/30 and optimal exact-reference law upper
rate remain open. Main18.2 moves from not_started to conditional;
coverage is87/167 unconditional and39 conditional, with151 confirmed
improvements. Original source bytes, dependency pins and the later
Palomar milestone are preserved.

Verified under Lean v4.36.0-rc2: full build passed (13841 jobs); direct axiom audit passed for 10823 declarations using only propext, Classical.choice and Quot.sound; all 9297 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 12.07 GiB.


## Actual divisor auxiliary polynomials, before component counting

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

Verified under Lean v4.36.0-rc2: full build passed (13857 jobs); direct axiom audit passed for 10850 declarations using only propext, Classical.choice and Quot.sound; all 9328 distinct ledger/evidence references checked; source-integrity and whitespace checks passed; Ubuntu free space 12.04 GiB.
