# Original integer-box rescaling and fixed logarithmic high-degree count

Sources: main13.4/main13.5, sources/main_sections/pair_rigidity.tex:211-256; internal P1-MATH-0496,0536 and exact existing polynomial linear-substitution/binary-budget lemmas. No new literature input is introduced. Original manuscript hashes remain preserved.

UniformPolynomialDilation constructs the actual uniform coordinate substitution P(c*x), its algebra automorphism for nonzero c, exact total-degree preservation and irreducibility preservation. Evaluation at the normalized point z/(2*N) is proved to equal the original polynomial evaluation at z. This provides an actual equation for the rescaled population, rather than assuming rescaling preserves the curve data.

QuadraticNormalizedGridBudget simplifies the internally proved global normalized-grid estimate to 300000*exp(4)*D^2*(Nat.log2(2*N)+1)*(k+1)^16. The singular/boundary budget, exceptional budget and component scale are combined by proved inequalities, retaining a genuinely quadratic degree power.

QuadraticRealIntegerGridCount transports every finite integer-vector population in the original closed box |z_i|<=N to the open unit box by dividing coordinates by 2*N. The actual map is injective; its image has exactly the original cardinality, lies on the normalized integer grid and vanishes on the constructed irreducible polynomial of the same degree. Applying the normalized theorem proves the original-box high-degree estimate, with no supplied rescaling, finite cover or population count.

LogarithmicQuadraticPlaneParameters proves exact doubling and quadrupling identities for the binary logarithmic budget L(N)=Nat.log2(N)+1. It chooses k=L(2*N), proves log(2*N)<=k and bounds the remaining logarithmic factors by 3^17*L(N)^17. For every irreducible real plane polynomial with L(2*N)<D, every original finite integer-box population therefore has cardinality at most (300000*exp(4)*3^17)*D^2*L(N)^17. The coefficient- and degree-uniform constant is explicit, and the order k is internally chosen.

The high-degree original real integer-box count is now complete. Combining the complementary low-degree range with the previously proved cubic arithmetic estimate, transporting between actual multivariate and nested-polynomial coordinates, and scalar descent to arbitrary characteristic-zero coefficient fields remain separate. Main13.4/13.5 are not yet promoted; the published all-field global theorem remains cubic with a<1/3.

P1-MATH-0537 adds four modules, fourteen theorems and three definitions. No numbered result is promoted. Coverage stays 161 proved, 3 conditional and 3 in_progress out of 167, with 164 completed. The project records 535 improvements and two P1 statement-scope corrections; the external BCN recurrence sign erratum stays separate. No new axiom, compiler change, dependency download, original source edit or Palomar submission is introduced.
