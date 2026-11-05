# Coefficient-height-free uniform counts for geometric elliptic conics

Source: main13.4 conic preparation. Removes coefficient height using the internally proved associated presentation, exact grid equality and negative-discriminant sign preservation.

UnrestrictedEllipticConicCount.natural_count proves the unconditional uniform N^epsilon bound for the actual full signed integer grid of every geometrically irreducible integer plane equation of exact total degree two and negative discriminant, with no restriction on any original coefficient. The threshold precedes the equation and the actual grid radius N. All original coordinate signs and axis points remain included.

Populations of at most four points are absorbed uniformly. Every larger population internally constructs a bounded-height associated equation with the same exact degree and geometric irreducibility. Rational association preserves the negative discriminant and gives equality of every original and replacement grid. The interpolation coefficient bound is polynomial in N with constants fixed solely by degree two; checkpoint393 then counts the replacement equation. The normalized equation, association, sign preservation, nonzero norm constant and imaginary norm count are all supplied internally.

finite_population_count proves the same bound for every actual finite population of original zeros in the symmetric N-box. polynomial_height_count proves the original-coefficient-unrestricted version in every fixed polynomial coordinate-height box B<=N^K, again choosing the threshold before the original equation and B. The small-box case is absorbed at a fixed threshold; the large-box case uses an explicit epsilon/(K+1) exponent budget.

Together with checkpoint389, this closes both nonzero-discriminant geometric conic branches with entirely unrestricted original coefficients. Parabolas of discriminant zero are still a separate obligation; no claim of a full conic or general BCN theorem is made. Original all-dimensional main13.4 remains open. No original numbered result is promoted.

P1-MATH-0394 adds three theorems. Coverage stays92 proved and72 conditional out of167, with164 completed and three in_progress. The ledger records392 improvements and two statement-scope corrections. No new axiom, unproved literature premise, dependency download, compiler change or original manuscript edit is introduced. Palomar remains deferred.
