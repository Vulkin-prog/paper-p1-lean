# Shifted polynomial determinant degree without domain assumptions

Source: main Theorem13.4, pair_rigidity.tex:214. This is preparatory algebra, not a proof of the original all-dimensional curve counting theorem. Original manuscript hashes remain preserved.

WeightedPolynomialDeterminantDegree.product_degree and determinant_degree prove a sharp shifted degree budget over every commutative coefficient ring. An entry in row i and column j only has to satisfy natDegree(entry)+r(i)<=c(j) when it is nonzero. If sum(c)<=T+sum(r), the determinant has degree at most T. Row and column shifts are integers, and the final degree bound is natural. The proof handles zero products explicitly and uses the signed permutation expansion, so neither a domain assumption nor a nonvanishing determinant hypothesis is required.

This is preparatory algebra for the degree-uniform intersection count needed in main13.4. It is designed to retain the Sylvester row and column offsets that are lost in the existing coarse maximum-entry bound. No resultant, finite Bezout bound, geometric point-count theorem or BCN input is claimed from this lemma alone. In particular, main13.4 remains in progress; the geometric Heath-Brown input and all other recorded unproved inputs remain open.

P1-MATH-0333 adds two checked algebraic lemmas. Baseline coverage stays89 proved and75 conditional out of167, with164 completed. The ledger records331 improvements and two statement-scope corrections. No new dependency, unproved input, axiom, compiler change or original manuscript edit is introduced. Palomar remains deferred.
