P1 V1.3 - finite checks of heterogeneous Bernoulli identities
===========================================================

Run from the source-archive root:

    python3 diagnostics/heterogeneous_formal_checks.py

No third-party package is required. The default output is
diagnostics/heterogeneous_formal_checks.json. A different location can be
chosen with --output PATH.

What is checked
---------------

The script evaluates eight explicitly defined finite joint laws of four,
five, or six Bernoulli variables, using exact rational arithmetic throughout.
The examples include different independent marginals, five identical events,
five mutually exclusive events, six overlapping affine events on five uniform
bits, and four reproducibly seeded arbitrary dependent joint distributions.
The latter are rational laws obtained by normalizing integer atom weights.

For each law, centered coefficients are computed directly as expectations of
products of J_i-p_i. The actual law of the sum is computed separately by
grouping its joint atoms. The script then checks:

1. The complete centered convolution identity, as an identity of all masses.
2. alpha = 2 sum_{i<j} c({i,j}) - sum_i p_i^2.
3. The exact heterogeneous formulas for the third and fourth factorial
   cumulants, including every repeated-index correction.
4. The mass, mean, and second factorial moment of the signed Bernoulli
   reference B2, and its third and fourth formal cumulants.
5. The factorial generating-function quotient used in the quartic proof,
   through degree four.

Factorial cumulants used as the independent comparison are computed from
factorial moments by the recurrence obtained from G'=K'G, where G=exp(K).
The generating-function quotient is evaluated by truncated exact polynomial
arithmetic. These computations are independent of the displayed formulas
being checked. There are 14 assertions per joint law, 112 assertions in all.

The JSON also records the exact marginals, mean, second, third, and fourth
factorial cumulants, signed and absolute pair activities, negative masses of
B2 when present, and incompatible triples with positive centered coefficient.
These last examples illustrate why no blanket negative-sign assertion is
made for incompatible centered coefficients.

Interpretation and limits
-------------------------

All 112 assertions passed in the recorded run. This is a reproducible finite
diagnostic of the algebraic identities. Their general proofs remain the
written formal and convolution arguments in exact_transfer.tex and
quartic_lower.tex. The script does not establish an asymptotic theorem,
check the arithmetic square-relation counts, extrapolate a fixed order to a
growing order, numerically certify an unspecified convolution-norm constant,
or certify the optimal Poisson approximation exponent.

The exact Python version is recorded in the JSON output. All probability and
polynomial operations use fractions.Fraction, so rounding error is absent.
