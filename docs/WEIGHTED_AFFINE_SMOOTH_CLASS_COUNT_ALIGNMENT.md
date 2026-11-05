# Exact weighted affine determinants and actual smooth-class point counts

Source: main13.4 affine integer point preparation. Reuses the internally proved smooth congruence determinant, exact exponent sums, finite integer kernel and finite plane intersection theorems.

AffineMonomialDeterminant proves the exact weighted determinant comparison for actual affine integer points. On the monomial rectangle 0<=i<=A,0<=j<=J, let k=(A+1)*(J+1) and W=sum(i+j). The module proves 2W=k*(A+J), and bounds the actual evaluation determinant by k!*B^W for every signed integer point population with both coordinates bounded by B. The estimate retains the individual row weights instead of giving every row the largest monomial weight.

The previously proved smooth affine congruence determinant theorem is reindexed onto this actual rectangle. Every point lies on the actual equation and in the specified residue class; a nonzero derivative modulo the prime is explicit. The determinant is divisible by p^(k*(k-1)/2), and comparison with the exact weighted real bound forces it to vanish. No determinant-vanishing property is assumed externally.

AffineSmoothClassAuxiliary constructs an actual nonzero integer coefficient vector annihilating the entire finite class from these vanishing minors. It then constructs an actual nonzero integer polynomial of partial degrees at most A and J, vanishing at every point of that class. Its existence does not use a supplied auxiliary equation or an unproved geometric covering statement.

AffineSmoothClassPointCount proves the actual finite intersection count using rational irreducibility of the original equation. When J is strictly below its outer degree, the auxiliary equation cannot be divisible by it. The proved finite plane intersection theorem therefore bounds the full smooth class by (degreeX G+degreeY G)*(A+J). Both signs and axis points are retained. Absolute irreducibility is not required for this local count.

This checkpoint proves the exact weighted local method. The global prime selection, avoidance of derivative divisors, summation over residue classes and improved eventual exponent remain separate obligations. No global1/D estimate, growing-degree BCN bound or original theorem13.4 is asserted here. No original numbered result is promoted.

P1-MATH-0399 adds three modules, nine theorems and three definitions. Coverage stays92 proved and72 conditional out of167, with164 completed and three in_progress. The ledger records397 improvements and two statement-scope corrections. No new axiom, external counting premise, dependency download, compiler change or original manuscript edit is introduced. Palomar remains deferred.
