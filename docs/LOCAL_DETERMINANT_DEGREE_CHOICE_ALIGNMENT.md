# Uniform auxiliary degree and avoidance power at the sharp exponent

Source: companion T1.4 geometric ingredient and the sharp exponent parameter choice in the local determinant method. Quantifier order puts H and m before the polynomial and coordinate height.

LocalDeterminantDegreeChoice.exists_auxiliary_degree proves that for every a>=0,b>=2 and epsilon>0 there is one H>=1 such that, with J=b-1,k=(H+1)*(J+1),N=k*(k-1)/2, N>=1 and H*k+a*J*k<=(2/b+epsilon/2)*N, J*k<=(epsilon/2)*N. H is chosen uniformly before the polynomial, its coefficient height and coordinate box. The proof uses an explicit large natural H and exact real inequalities; no limiting argument or parameter-existence premise is assumed.

triangle_weight proves positivity and the exact real identity2*N=k*(k-1), including the natural division by two. exists_avoidance_power proves that whenever beta>0 and alpha>=beta there is one m>=1 satisfying A<=alpha*m and B<=beta*m for arbitrary prescribed natural exponents A,B. Applying this with A=a*b+a+1,B=b+1,alpha=2/b+epsilon/2,beta=epsilon/2 gives the remaining obstruction exponent budget.

Together with checkpoint359, these choices provide the uniform exponents needed for both strict prime comparisons. The final wrapper must still choose the two degree-only coefficient constants, round the common prime base and invoke the proved global finite-prime count before the sharp b>=2 input is discharged.

P1-MATH-0360 adds three theorems. Coverage stays89 proved and75 conditional out of167, with164 completed. The ledger records358 improvements and two statement-scope corrections. No axiom, unproved literature premise, dependency download, compiler change or original manuscript edit is introduced. Main13.4 remains open and Palomar remains deferred.
