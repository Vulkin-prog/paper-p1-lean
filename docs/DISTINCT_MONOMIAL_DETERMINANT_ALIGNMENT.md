# Distinct-monomial determinant expansion and coefficient-uniform chart bound

Source: companion T1.4, companion_sections/arithmetic_appendix.tex:139, Step2 auxiliary extraction and its coefficient-height/parameter-order ledger; T1.5 uses that extraction. Original source hashes remain preserved.

The finite polynomial part of the relative-chart determinant estimate is now proved, with an explicit constant depending only on the selected degrees. The remaining weighted lattice-sum estimate and degree selection remain explicit obligations.

WeightedEvaluationDeterminant expands the determinant of a finite polynomial evaluation matrix by multilinearity. Any selection repeating a monomial row contributes zero; an exact sum over injective selections is proved. A row-weight determinant inequality and a coefficient-height bound give a uniform bound by the product of the selected monomial weights, multiplied by an explicit finite constant. No source-population cardinality or moving original coefficient enters that constant.

DeterminantChartExpansion proves the exact finite binomial expansion of (1+alpha)^a*(1+2*alpha+alpha^2+beta)^b on the rectangle 0<=k<=A+2B, 0<=j<=B. The actual nonnegative integer coefficient is choose(b,j)*choose(a+2*(b-j),k), uniformly bounded by 2^(A+3B). Both the exact evaluation identity and the coefficient bound are checked.

DeterminantChartBound assigns the monomial weight exp(-(r1*k+r2*j)). If the two actual errors have absolute values at most exp(-r1) and exp(-r2), the corresponding monomial evaluations satisfy those weights. Its normalized determinant is at most C(A,B)*exp(-L) whenever every injective selection of H=(A+1)*(B+1) monomials has total logarithmic cost at least L. The explicit constant is

  ((A+2B+1)*(B+1))^H * 2^((A+3B)*H) * H!.

The actual original-variable determinant factors exactly by the product of the column scalings s0^a*t0^b; its absolute bound is transported with that factor. The weighted-cost hypothesis is a finite combinatorial inequality, not an assumed determinant or solution-count theorem. Its sharp lower bound, the subsequent fixed-degree choice and the strict comparison with integer row denominators still need proof. Existing exact quadratic-chart identities supply the intended original-equation substitution.

P1-MATH-0238 isolates and proves this finite coefficient-uniform determinant step. No published fixed-coefficient theorem is used to discharge the moving-coefficient extension. T1.4 and T1.5 remain in progress; coverage stays89 proved and72 conditional out of167, with six incomplete numbered results. There are237 improvements and one statement-scope correction. No external input, axiom, Paper C port, dependency download, compiler change or original manuscript edit is introduced. Palomar remains deferred.
