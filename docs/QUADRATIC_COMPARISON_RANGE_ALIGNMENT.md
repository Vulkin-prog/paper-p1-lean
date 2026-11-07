# Make the exact quadratic-exponent comparison range explicit

Source: corrected companion T5.1 and the discussion of its exact exponent comparison. This is a qualification of real-parameter necessity, not a new false numbered result.

The corrected capped quadratic-kernel comparison is valid for every real beta and delta. The uncapped comparison is valid whenever beta-2*delta<=2. QuadraticComparisonRange.exponent_le_affine_iff_of_nonneg_delta now proves that, for nonnegative delta, this condition is also necessary. The proof treats the exact min/max exponent and affine expression, without a limiting exponent margin.

QuadraticComparisonRange.actual_delta_nonneg proves the required sign for every actual positive prescribed divisor e at scale N>=2. Consequently actual_comparison_iff identifies the exact criterion for the original actual parameter delta=log(e)/log(N), uniformly in every real beta. This makes the distinction between a real-parameter algebraic statement and the admissible arithmetic parameters explicit.

The sign hypothesis matters for necessity on the entire real plane: at beta=delta=-4, the uncapped exponent is zero and is at most the affine value 3/2, although beta-2*delta=4>2. This is not an admissible positive-divisor counterexample and does not refute either counting estimate. The earlier actual admissible delta=0 counterexample to the unrestricted original display remains unchanged.

This is a parameter-scope clarification for the revised discussion, not a third false original numbered statement. Revised coverage remains 167/167 proved; the original v1.6 ledger remains 165 proved, 0 conditional and 2 false-original scopes in_progress. The original source bytes and compiler pin are preserved. The first analytic registry family has already passed local Comparator and Lean/NanoDa replay; further families and the complete pinned Palomar workflow remain. No registration is claimed.
