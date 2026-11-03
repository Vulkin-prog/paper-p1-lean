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
