# Exact signed norm coordinates and height budgets for conics

Source: main13.4 plane preparation and its remaining conic branch. The new identities use actual integer coefficients and signed integer points, with no assumption on the sign of the quadratic norm coefficient.

ConicNormCoordinates constructs the actual integer transformation of a general equation a*x^2+b*x*y+c*y^2+d*x+e*y+f=0 to a signed quadratic norm equation. With Delta=b^2-4*a*c, beta=2*b*e-4*c*d, gamma=e^2-4*c*f and delta=beta^2-4*Delta*gamma, the coordinates are u=2*Delta*x+beta and v=2*(2*c*y+b*x+e). norm_identity proves the exact identity u^2-Delta*v^2=delta-16*c*Delta*Q(x,y); every original zero therefore maps to the literal norm equation. No sign restriction on Delta or the coordinates is introduced.

transform_injective proves that all actual signed integer solutions remain distinct when c and Delta are nonzero. For the explicitly defined sum height M of the six coefficients, the internally proved bounds are |Delta|<=5*M^2, |beta|<=6*M^2, |gamma|<=5*M^2 and |delta|<=136*M^4. Every point with coordinate absolute values at most H maps to |u|<=(10*H+6)*M^2 and |v|<=(6*H+2)*M. All bounds use natural absolute values and retain exact integer arithmetic.

These are algebraic and height-transport theorems preparing the outstanding conic branch of the unconditional plane route. They assert no conic counting estimate. Extracting this presentation from an actual polynomial, treating the zero-discriminant cases, and counting both signs of the norm coefficient remain subsequent obligations. The stronger BCN property and original all-dimensional main13.4 remain open.

P1-MATH-0380 adds ten theorems and nine definitions/structures. Coverage stays92 proved and72 conditional out of167, with164 completed and three in_progress. The ledger records378 improvements and two statement-scope corrections. No axiom, unproved literature premise, dependency download, compiler change or original manuscript edit is introduced. Palomar remains deferred.
