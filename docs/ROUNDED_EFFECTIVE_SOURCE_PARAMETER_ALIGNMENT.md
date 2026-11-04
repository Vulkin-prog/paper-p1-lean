# Literal rounded effective parameter and one uniform threshold for every gcd reduction

Source: companion T1.4, companion_sections/arithmetic_appendix.tex:139, first-degree-one auxiliary-factor elimination in Step3; T1.5 uses that reduction. Original source hashes remain preserved.

The effective parameter after the actual gcd reduction is now a literal natural integer with checked size and logarithmic bounds. One threshold makes it large enough for ANY preselected primitive-count threshold, simultaneously over every reduction scale dividing the short shift.

ReducedSourceParameter defines effective(N,s)=N/s over the reals and parameter(N,s)=ceil(effective(N,s)). Positivity, the lower ceiling bound and the upper bound parameter<=2*effective when effective>=1 are proved. For a positive integer reduction scale, the rounded parameter is at most the ORIGINAL integer N. The exact logarithm of the unrounded quotient and the bound log(N)-log(parameter)<=log(s) are retained, including the rounding in the latter inequality.

If the reduction scale s is at most a positive shift of size at most sqrt(N), then BOTH the unrounded and rounded effective parameters are at least sqrt(N). Consequently the rounded parameter has logarithm between log(N)/2 and log(N). If L^2<=N it is at least the preselected natural threshold L. These inequalities are proved for the literal rounded parameter rather than a real replacement.

The final uniform theorem uses the internally proved logarithmic-power estimate: for ANY fixed short-shift parameters and ANY fixed target threshold L, one N0 precedes N, the actual short shift and EVERY integer reduction scale s<=h. It gives parameter>=L, parameter<=N, positivity and both logarithmic comparisons simultaneously. With s=g^2*q fromP1-MATH-0290, this closes the effective-parameter threshold order required to apply the primitive determinant theorem uniformly on all actual gcd families.

P1-MATH-0291 is UNCONDITIONAL and uses no counting input. The full reduced source Box, uniform transfer of the source barrier and short shift, exponential-shape comparison and final sum over reductions remain open. The two ordinary inputs retained by the primitive determinant theorem still have unformalized proofs. T1.4 and T1.5 stay in progress; coverage remains89 proved and72 conditional out of167. There are290 improvements and one statement-scope correction. No new external input, axiom, dependency download, compiler change or original manuscript edit is introduced. Palomar remains deferred.
