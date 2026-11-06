# Actual iterated reciprocal differences have exact derivatives and rising-factorial coefficients

Source: internal preparatory analytic route for companion T19.17. This is not a completed additional manuscript result.

Define the ACTUAL reciprocal finite-difference kernel recursively from 1/x^m by K(h::hs,m,x)=K(hs,m,x)-K(hs,m,x+h), and its exact coefficient recursively. For nonnegative shifts and x>0, prove its ACTUAL derivative is -m*K(hs,m+1,x) and it is continuous on the positive half-line. The coefficient is nonnegative and is EXACTLY m.ascFactorial(length hs)*product(hs). Six theorems and two definitions establish these identities, including the reciprocal-power derivative, with no external oscillation input.

The triple-large prime frequency contribution, the central-frequency mean comparison and complete logarithmic short-average concentration remain unproved. T19.17 conditional; original T1.7 unconditional. Coverage: 164 proved, 1 conditional, 2 in_progress /167; all 73 main proved. Sources, false-scope corrections, compiler and axioms unchanged. About 51.31 GiB free on Ubuntu. No dependency download or Palomar registration.
