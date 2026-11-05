# Actual bounded-height plane equation from the original grid kernel

Source: main13.4 and the coefficient-height reduction for its geometric plane specialization. Original signed grid populations and the exact total-degree cap are retained.

BoundedPlaneInterpolation.exists_bounded_equation constructs a nonzero integer equation Q of total degree at most D through every point of an arbitrary finite signed integer population S in the coordinate box B>=1, whenever one nonzero original equation P of total degree at most D vanishes on S. Its coefficient height is at most(3*r*(B^D+1))^(r-1), r=card(TotalDegreeMonomials.Index D), independently of every coefficient of P and independently of the number of points. All points are retained.

minor_vanishing uses the actual coefficient vector of P, proves it nonzero by exact triangular reconstruction, and proves it is an integer kernel vector of each actual square row minor. An actual nonzero coordinate and the checked adjugate identity force each minor determinant to vanish. No minor, rank or interpolation assumption is supplied. exists_coefficients applies the previously proved finite integer annihilator theorem to the whole family with explicit row bound B^D+1. The triangular basis recovers Q with exact degree and height control. entry_bound handles arbitrary coordinate signs. heightBound_polynomial bounds the explicit height further by(6*r)^(r-1)*B^(D*(r-1)), with constants and power depending only on D.

This closes the bounded-height interpolation construction. Its application via finite plane Bezout to restrict the remaining geometric integer counting input to polynomially bounded coefficients still needs to be assembled. The actual BCN counting bound and general main13.4 remain unproved.

P1-MATH-0368 adds five theorems and two literal entry/height-bound definitions. Coverage stays92 proved and72 conditional out of167, with164 completed and three in_progress. The ledger records366 improvements and two statement-scope corrections. No axiom, unproved literature premise, dependency download, compiler change or original manuscript edit is introduced. Palomar remains deferred.
