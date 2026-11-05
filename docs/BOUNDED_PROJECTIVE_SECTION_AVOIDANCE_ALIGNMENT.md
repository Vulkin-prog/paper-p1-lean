# Bounded integer linear coordinates avoiding complete projective sections

Sources: remaining main13.4; internally proved actual finite projective sections P1-MATH-0542; genuine polynomial roots and actual integer height estimates. No external projection result is assumed. Original manuscript hashes remain preserved.

BoundedFieldPolynomialNonvanishing proves that an actual nonzero polynomial of degree at most M over any characteristic-zero field is nonzero at one of the literal integers 0,...,M. This uses actual root inclusion, injective integer casts and the proved root-count bound.

BoundedMomentLinearForm assigns to every nonzero vector w in F^n its actual moment polynomial sum_i w_i T^i. The coefficients, evaluation, degree at most n-1 and nonvanishing are all proved. The product over an actual finite vector family S has degree at most (n-1)*|S|. The integer nonroot theorem supplies one t at most this bound for which every moment polynomial is nonzero. The actual integer coefficient vector u_i=t^i therefore avoids every vector in S, with each coefficient at most ((n-1)*|S|+1)^(n-1).

IntegerLinearFormHeight proves the actual integer evaluation bound: if 0<=u_i<=B and |v_i|<=H, then |sum_i u_i v_i|<=n*B*H. The conclusion concerns the genuine multivariate linear polynomial and original integer coordinates.

BoundedProjectiveSectionAvoidance applies this construction to the internally constructed complete actual projective section locus. For a homogeneous prime curve ideal with its genuine linear Hilbert polynomial D*r+b and an actual homogeneous degree-e equation outside that ideal, one nonnegative integer coefficient vector avoids every point of the entire projective section, with each coefficient at most ((n-1)*e*D+1)^(n-1). The same coefficients work for every height H and every original integer vector, with the proved height cost n*((n-1)*e*D+1)^(n-1)*H. A corollary retains the actual rational ProjectiveCurveData model and its internally derived integer Hilbert degree. The coefficients are chosen before H and before any finite population; no supplied exceptional-point list or projection-height premise is used.

This closes a bounded integer coordinate-selection step needed for controlled higher-dimensional projection. Actual finiteness and birationality of the projected curve, scalar-extension degree transport and the complete all-dimensional counting theorem remain separate. Main13.4 and companionT1.7/T19.17 stay unresolved; main13.5 remains fully internally proved.

P1-MATH-0543 adds four modules, eleven theorems and one definition. No numbered result is promoted. Coverage stays 162 proved, 2 conditional and 3 in_progress out of 167, with 164 completed. The project records 541 improvements and two P1 statement-scope corrections; the external BCN recurrence sign erratum stays separate. No new axiom, compiler change, dependency download, original source edit or Palomar submission is introduced.
