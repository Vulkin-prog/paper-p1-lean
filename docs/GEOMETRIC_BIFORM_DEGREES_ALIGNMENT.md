# Positive partial degrees for every geometric plane curve of total degree at least two

Source: main13.4 and the biform application to its geometric plane specialization. Actual total and partial degrees, coefficient extensions and coordinate swaps are checked exactly.

GeometricBiformDegrees.positive_partial_degrees proves that every irreducible plane equation of total degree at least two over an algebraically closed field has both partial degrees positive. univariate_degree_one proves the excluded case exactly: if the outer degree is zero, irreducibility reflects to the single-variable polynomial and algebraic closedness forces actual total degree one. outer_degree_pos applies this contradiction.

constant_outer_degree computes the actual total degree of a nested constant polynomial, and constant_irreducible_reflection proves irreducibility reflects through the outer constant embedding using the evaluation retraction. integer_outer_degree_pos and integer_positive_degrees transport the result to the original actual signed integer biform under its geometric projective irreducibility, with exact coefficient-map degree preservation and actual coordinate swap.

These algebraic facts allow the complete proved Heath-Brown input to be applied to every absolutely irreducible integer plane curve of total degree at least two. A fixed-degree coefficient-uniform weaker plane bound is the next application; the stronger degree-uniform BCN estimate is not proved by this module.

P1-MATH-0371 adds seven theorems. Coverage stays92 proved and72 conditional out of167, with164 completed and three in_progress. The ledger records369 improvements and two statement-scope corrections. All artifacts were already available locally. No axiom, unproved literature premise, dependency download, compiler change or original manuscript edit is introduced. Main13.4 remains open and Palomar remains deferred.
