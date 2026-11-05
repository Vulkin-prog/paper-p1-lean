# Actual prime-obstruction height from coefficients and the first pair

Source: companion T1.4 geometric ingredient and the integer-height bound used to choose usable primes in the local determinant method. The derivative and signed projective coordinates are literal.

ProjectivePrimeHeight.badInteger_bound proves the explicit bound |K(G,z)|<=(a+1)*(b+1)*b*height(G)*L^(a+1)*Y^b, where a=degreeX G,b=degreeY G>0 and the original signed pairs lie in absolute boxes L,Y>=1. K is the actual denominator-times-projective-derivative integer introduced in checkpoint355. No obstruction-size or prime-avoidance hypothesis is assumed.

derivative_height proves height(G.derivative)<=b*height(G) by exact coefficient differentiation, including coefficients outside the actual degree. projective_evaluation_bound proves the literal double homogeneous evaluation bound using the original partial degrees and the exact coefficient height. badInteger_bound combines these with the degree drop in the differentiated second variable. nonexceptional_bound substitutes the proved root-height box Y=(a+1)*height(G)*L^a on every original point whose two endpoint evaluations are nonzero. It requires no second-coordinate box as an input.

This provides the actual polynomial-size obstruction bound required by the uniform dyadic prime avoidance construction. The two numerical comparisons with the prime base still need to be chosen simultaneously with the final exponent parameters. The global sharp b>=2 bound is not claimed yet.

P1-MATH-0357 adds four theorems. Coverage stays89 proved and75 conditional out of167, with164 completed. The ledger records355 improvements and two statement-scope corrections. No axiom, unproved literature premise, dependency download, compiler change or original manuscript edit is introduced. Main13.4 remains open and Palomar remains deferred.
