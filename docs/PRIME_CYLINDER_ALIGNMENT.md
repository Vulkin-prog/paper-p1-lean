# A rare arithmetic cylinder and the original exponential moments

Target: companion Proposition T19.7, page 71, `p1:limits:cylinder`,
`companion_sections/limits_appendix.tex:385`. Original statement SHA-256:
`c4dfa742ae68556d196927fdaaae789b2734586e0e9820cdff17c2218e8639be`.

For every fixed t>2, N_q=2^(q-1) and L_q=q-1, the source asserts a
scaled logarithmic liminf at least (t-2)*log 2>0 along odd primes.
The same conclusion concerns positive runs alone.

## Actual events and exact cylinder probability

`OneNegativePrime.sample` assigns the negative sign to q and the positive
sign to every other prime up to the finite cutoff. Its value at n is
exactly the parity of v_q(n). If q divides neither u nor u+1, the start
q*u+1 has a negative predecessor, q-1 positive values and a negative next
value. The actual run event, its sign and the next value are proved in
`positive_exact_run`.

`PrimeRunStarts` constructs a finite subset of these starts in [N,2N).
Two residue-class counts, integer floors and injectivity give the fully
finite bound K>=N/q-2N/q^2-4. This bound replaces the source O(1) argument
without asserting an asymptotic formula for the entire start population.

`PrimeCylinderSize` identifies the prime-coordinate cardinality with
the paper's pi(M). The atom has exact mass 2^(-pi(M)).
`PositiveStarts` defines the actual positive-run indicator, infinite
count and Bochner exponential moment, and proves their finite-cylinder
transfer. `PrimeRunCylinder` gives

    log E exp(t Z_positive) >= t*K - pi(M)*log 2.

This is proved from the mass of the actual atom and positivity of the
finite expectation. Joint independence of starts is not a hypothesis.
Pointwise positive-count domination gives the same total-count bound.

The formal cutoff is the existing sufficient dyadic cutoff
M=2N+L=2N+q-1. The manuscript uses 2N+q. Both contain every integer used
by the windows; the one-unit difference has the same proved asymptotic
cost. Original source bytes are unchanged.

## Limits, prime restriction and divergence

`PrimeCylinderScale` proves N_q->infinity, q/N_q->0,
log(N_q)/q->log 2, M/N_q->2 and log(M)/log(N_q)->1.
The internally proved sharp prime number theorem then yields

    (log N_q)/N_q * pi(M_q)*log 2 -> 2*log 2.

`PrimeCylinderDivergence.startLower_tendsto` proves the scaled start
bound tends to log 2. Thus `lowerRate_tendsto` has limit
(t-2)*log 2. The finite lower bounds apply to the original two moments.

`companion_T19_7` makes the epsilon and prime-index quantifiers explicit:
for every epsilon>0, one q_0 works for all primes q>=q_0 and both counts.
`PrimeCylinderLiminf` proves the odd-prime filter is nontrivial using
Euclid's theorem and states the literal liminf inequality in EReal.
The extended real formulation permits an infinite liminf without any
unproved upper bound. `companion_T19_7_liminf` also states strict
positivity of the source constant. `logarithms_diverge` and
`moments_diverge` prove that both original observables eventually exceed
every prescribed real level along the primes.

No cylinder weight, start-count bound, PNT estimate or target limit is
an explicit premise. No new Paper C source is ported. Mathlib at the
pinned revision supplies elementary divisibility, finite sums, real
limits, extended reals and infinitude of primes. The sufficient threshold
t>2 is retained; its optimality is not asserted. The later arithmetic
large-component construction is a separate result.

## Validation

The full Lean v4.36.0-rc2 build passed (9,029 jobs). The actual axiom
audit passed for all 2,602 theorem/lemma declarations, allowing only
`propext`, `Classical.choice` and `Quot.sound`. All 572 distinct names
in the coverage and mathematical-finding ledgers were checked directly
by Lean. Source integrity checks passed for 138 manifest entries and
all 167 original numbered statement hashes. Numbered coverage is
40 / 167: article 15 / 73, companion 25 / 94. No new mathematical
correction is asserted at this checkpoint, and no Palomar registration
is made. Available Ubuntu-root space is 17.95 GiB.

Validated implementation of companion T19.7:
[af00f6613fc890bee31ac2b83d609dc9a9030635](https://github.com/Vulkin-prog/paper-p1-lean/commit/af00f6613fc890bee31ac2b83d609dc9a9030635).
