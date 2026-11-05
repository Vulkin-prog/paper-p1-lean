# Polynomial-size prime covers for complete affine point populations

Source: main13.4 quantitative degree-uniform preparation. Combines the internally proved ordinary PNT, actual finite prime subsets, distinct-prime avoidance and the full weighted affine class count.

PolynomialPrimeCover proves an actual finite prime cover with an absolute threshold chosen before both the scale P and the number m of requested primes. For P above that threshold and m^2<=P, it constructs exactly m distinct primes in (P,16P], with total sum at most16*m*P. Every nonzero integer of absolute value less than P^m is avoided by at least one actual selected prime. No prime-supply or avoidance property is a premise.

The proof uses the already internally proved PNT for the ordinary inclusive prime-count function. Uniform two-sided prime-count bounds imply that (P,16P] contains at least2P/log P primes for all sufficiently large P. The elementary logarithm/square-root inequality then gives at least sqrt(P) primes. An actual m-element subset is selected. Its prime product is at least P^m, and the proved distinct-prime divisibility argument supplies avoidance. All cardinalities concern actual finite prime sets.

PolynomialPrimeAffineCount.uniform_bound substitutes this proved pool into the complete actual signed affine counting argument. The absolute pool threshold precedes every equation, bidegree, auxiliary rectangle, point height and finite population. Under m^2<=P and the two explicit determinant and obstruction comparisons, the full population is bounded by the existing degree-only exceptional term plus (degreeX G+degreeY G)^2*(A+J)*(16*m*P). The earlier2^m multiplier is absent. Every critical point, sign and axis point remains included.

Together with checkpoint403's absolute local determinant scale, this removes two unnecessary exponential parameter costs. The final coefficient normalization, degree factors and global growing-degree estimate remain quantitative obligations. No D^2 logarithmic BCN theorem, original growing-degree corollary or sharp half-window rank consequence is asserted here.

P1-MATH-0404 adds two modules, seven theorems and one definition. Coverage stays93 proved and71 conditional out of167, with164 completed and three in_progress. The ledger records402 improvements and two statement-scope corrections. No new axiom, unproved analytic premise, dependency download, compiler change or original manuscript edit is introduced. Palomar remains deferred.
