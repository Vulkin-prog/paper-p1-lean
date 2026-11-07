# Exact valuation criterion for the retained positive starts

Checkpoint P1-MATH-0988 strengthens the finite construction for companion T19.7.
The positive multiplier guard u>0 is explicit: at u=0 the natural-number
factorization convention does not represent the preceding multiplicative value.
Every multiplier in the actual retained interval is automatically positive.

For a positive multiplier u in the one-negative-prime sample, the positive run-start condition at q*u+1 with length at least q-1 is equivalent to an even q-adic valuation of u. The earlier q not dividing u condition is only sufficient. Retaining every multiplier with even valuation in the same parameter interval enlarges the forced start set. The same supported cutoff M=2*q*floor(N/q), exact cylinder probability and actual expectation monotonicity give the stronger cardinality-based lower bounds for both full moments. The earlier explicit real lower count N/q-N/q^2-3 remains valid. At N=18, q=3 the start 28 is added, because u=9 has valuation two. The retained cardinality and corresponding exponential lower bound are strictly larger for every t>0. The original prime-scale t>2 asymptotic theorem and coefficient are preserved.

The new retained parameters satisfy parityVec(u)(q)=0, proved equivalent
to Even(u.factorization(q)). The exact positive-start equivalence includes
the preceding negative sign and the following q-1 positive values. The
right endpoint is unrestricted, as required by the actual observable.

The older one-sided start set is contained in the new set. Its finite
lower count is therefore preserved. Every new retained start still uses
only integers through M=2*q*floor(N/q), so the exact cylinder probability
remains 2^(-primeCount(M)). The retained subcount is integrated first and
then compared to both actual full moments for t>=0. No smaller-cylinder
dependence of the full count is assumed.

At N=18 and q=3, the multiplier u=9 has even valuation two. The start
x=28 belongs to the new retained set and is absent from the earlier
coprime set. Finite set inclusion and this witness prove a strict
cardinality gain, hence a strictly stronger exponential lower bound for
every t>0 at the same cylinder cost. No precise new density or improved
asymptotic threshold is asserted.

Canonical declarations include positive_start_iff_even_factorization,
positive_exponential_card_lower, total_exponential_card_lower and
strictly_stronger_card_bound_example in PaperP1.ValuationPrimeCylinder.

Full Lean v4.36.0-rc2 replay passed at source 57835da7813e314367f689312af436f9ae62e869: 18,571 build jobs, 19,513 source-discovered theorem axiom checks and 19,660 distinct declaration-reference checks, all actual process exits 0. Proof warnings are errors; only propext, Classical.choice and Quot.sound occur.

The full replay and original compressed logs are preserved in [the validation record](validation/checkpoint-0988/validation.json).
