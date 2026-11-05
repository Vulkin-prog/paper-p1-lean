# Sharp bivariate resultant degree from actual total degrees

Source: main Theorem13.4, pair_rigidity.tex:214. Preparatory elimination algebra only; the original integral-curve counting theorem remains unproved. Original source hashes are unchanged.

BivariateResultantDegree.resultant_degree proves natDegree(resultant(P,Q))<=D*E when the actual total degrees of P and Q are at most D and E. It applies over every commutative coefficient ring, uses the actual default outer degrees in the Sylvester matrix, and needs no irreducibility, domain, nonzero resultant or full-degree leading coefficient. The total degree is exactly the existing PlaneCurvePointCount.degree, with no replacement definition.

The five new lemmas give the coefficient-row degree constraint, the outer-degree bound, the integer Sylvester shift budget, the individual nonzero-entry constraint, and the final determinant bound. The budget uses (D-m)*(E-n)>=0 for the actual outer degrees m,n. It therefore retains the cancellation of row and column shifts even when m<D or n<E. This improves the earlier coarse resultant-degree estimate based on one maximum entry degree.

This is preparatory elimination algebra for main13.4. A nonvanishing resultant, an injective projection of a finite point set, the finite Bezout count and the geometric BCN theorem still need their separate arguments. No BCN point-count input is discharged here, and the original all-dimensional integral-curve statement remains in progress. Coverage stays89 proved and75 conditional out of167, with164 completed. The ledger records332 improvements and two statement-scope corrections. No original source, compiler, dependency, axiom or remaining input is changed; Palomar remains deferred.
