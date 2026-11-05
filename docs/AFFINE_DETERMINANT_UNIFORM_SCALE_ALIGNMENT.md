# Degree-uniform local affine determinant prime scale

Source: main13.4 degree-uniform preparation. Refines the internally proved exact affine monomial weights and smooth determinant valuation by a factorial-to-triangular-power bound.

AffineDeterminantUniformScale removes the factorial-dependent prime constant from the exact local affine determinant comparison. For every k, it proves k!<=2^(k*(k-1)/2) by an actual induction and an exact triangular-number identity. The factorial is therefore paid for by a fixed base raised to the same valuation already supplied by the smooth determinant theorem, rather than by a constant chosen above k!.

For every outer degree b>=2 and auxiliary first degree A>=1, with J=b-1, k=(A+1)*b and v=k*(k-1)/2, the actual monomial weight satisfies W<=(1/b+1/(A+1))*v. All degrees are quantified in the theorem; no constant is chosen after b. If H>=1 and log H<=A+1, then H^(1/(A+1))<=exp(1). Consequently P>=3*exp(1)*H^(1/b) forces the actual numerical determinant comparison k!*H^W<P^v. The prime-scale constant3e is absolute and independent of the degree and auxiliary rectangle.

exists_logarithmic_degree constructs an actual natural A with 1<=A, log H<=A+1 and A<=log H+2. Thus the local weighted method needs an auxiliary degree only logarithmic in the height. The new comparison is available for the actual local determinant and auxiliary constructions already proved in checkpoints399-400.

This is a degree-uniform local comparison, not a global BCN bound. The number and sizes of primes needed to avoid actual bad reductions, the residue-class sum and the final degree factors remain separate quantitative obligations. The full D^2 logarithmic BCN theorem and original all-dimensional main13.4 remain open. A substantially larger polynomial degree factor would not suffice for the source sharp half-window rank argument, whose extraction exponent approaches1/2; no such rank consequence is asserted.

P1-MATH-0403 adds six theorems. Coverage stays93 proved and71 conditional out of167, with164 completed and three in_progress. The ledger records401 improvements and two statement-scope corrections. No new axiom, external counting premise, dependency download, compiler change or original manuscript edit is introduced. Palomar remains deferred.
