# Connected normalized value unions and exact affine probabilities

The common-value hypothesis in the general finite affine probability
lemma is weakened to connected overlap. Define the actual intersection
graph of a finite family of nonempty value sets. Whenever this graph is
connected, the even square-class image of their union equals the sum
of the individual even images. A checked propagation along graph walks
proves this identity; private primes are not needed for the identity.

For positive integer-normalized windows, private normalized union and
absence of predecessor/internal collisions already supply actual affine
compatibility. Connected overlap now gives the exact total rank
union.card-1 and hence actual probability 2^(-(union.card-1)), even when
no value belongs to every normalized window. The corresponding exact
p^r*2^rho identity retains the literal rank/nullity equation.

This extends P1-MATH-0098 and the rational-witness tools without counting
a new improvement. The rational positive connected lower bound remains
unconditional; the lower bound for the total third factorial cumulant
and the full aligned-triple estimate remain open. Coverage stays 79/167
and confirmed improvements stay 98. No source manuscript, external
premise, dependency version or Palomar state changes.

Verified with Lean v4.36.0-rc2: full lake build (11131 jobs), actual axiom audit of all 7287 theorem/lemma declarations, direct Lean checks of all 5004 ledger/finding references, source integrity (138 manifest entries and 167 numbered statements), and git diff --check. Only propext, Classical.choice and Quot.sound occur. Ubuntu root space after verification: 14.86 GiB.
