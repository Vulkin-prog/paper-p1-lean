# Actual reduced unimodular bases with a globally shortest first vector

Source: companion T1.4, companion_sections/arithmetic_appendix.tex:139, lattice-coordinate and uniform auxiliary-height steps; T1.5 uses that reduction. Original source hashes remain preserved.

Every invertible real image of the integer plane now has an actual reduced unimodular integer basis. Its first image vector is globally shortest, the second is constructed by nearest-integer reduction, and the length/projection/area inequalities are all proved. The length-order premise of the previous geometric lemma is discharged internally.

BinaryBasisShear constructs the actual integer shear and its inverse, proves determinant one, and verifies both column identities. It transports the shear through any real lattice matrix and proves the exact oriented-area identity for the real images of integer matrix columns. Integer inverse matrices force each column to be nonzero. The explicit primitive Bezout completion has determinant one.

ReducedBinaryLatticeBasis defines the actual reduced integer matrix and inverse using the nearest integer of the projection ratio. Both inverse products and determinant one are proved. Its first column is unchanged; its second real image is exactly the reduced vector used in the proved nearest-integer geometry.

The existence theorem constructs a primitive globally shortest vector by the finite minimization from P1-MATH-0252, completes it to an actual integer basis, and applies the actual shear. The reduced second integer column is nonzero, so global minimality supplies the required length order. If v,w are the two real basis vectors, the theorem proves

  0 < |v|^2 <= |w|^2,
  |<v,w>| <= |v|^2/2,
  3*|v|^2*|w|^2 <= 4*det(T)^2.

It also retains global minimality of the first vector among ALL nonzero integer lattice vectors. Neither a shortest-vector nor a reduced-basis hypothesis is supplied to this existence theorem: an actual real left inverse of T is sufficient.

P1-MATH-0253 closes the existence and elementary geometry of the reduced binary lattice basis. Polynomial coefficient-height control AFTER the nearest-integer shear, the exact lattice coordinate boxes and their source-scale specialization remain to be assembled, followed by geometric curve counts and interval sums. T1.4 and T1.5 stay in progress. Coverage stays89 proved and72 conditional out of167, with six incomplete numbered results. There are252 improvements and one statement-scope correction. No external input, new axiom, dependency download, compiler change or original manuscript edit is introduced. Palomar remains deferred.
