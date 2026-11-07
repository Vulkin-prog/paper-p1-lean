# Effective density of the retained forced starts

Checkpoint P1-MATH-0990 strengthens the construction for companion T19.7.
All 167 original and revised numbered statement blocks are preserved.

For a prime q<=N, let m=floor(N/q), and retain the positive multipliers in
[m+1,2*m) whose q-adic valuation is even. Let C be the cardinality of their
actual image starts q*u+1 in ValuationPrimeCylinder.starts(N,q). Define

```text
k(N,q) = (Nat.clog q N + 1) / 2
L(N,q) = (N-1)/(q+1) - 3*k(N,q).
```

Here Nat.clog is the integer ceiling logarithm, and the division defining
k is natural-number division. The depth therefore equals the ceiling of
half that integer logarithm. Every retained multiplier is positive and
less than N, whereas q^(2*k)>=N. Its even valuation is consequently 2*j
for exactly one j<k. The finite union of these disjoint layers equals the
complete retained parameter set. This equality precedes the count bound.

The exact translated-interval multiple counts give

```text
(N-1)/(q+1) - 3*k <= C <= N/(q+1) + 2*k,
abs(C - N/(q+1)) <= 3*k + 1/(q+1).
```

For t>=0, both full actual exponential moments are at least
exp(t*L(N,q)-primeCount(M)*log(2)), using the same supported cylinder
M=2*q*floor(N/q). No target count or probability inequality is an input.
The automatically chosen depth gives a complete cover; it need not
maximize the earlier finite-depth lower budget among all depths.

For each fixed prime q, the normalized deterministic count C/N tends to
1/(q+1). More strongly, for every prime q<=N,

```text
abs(C/N - 1/(q+1)) <= (3*k(N,2)+1)/N -> 0.
```

Thus the approximation threshold depends only on the requested absolute
error, before N and q are quantified. This concerns the retained forced
subset on the specified cylinder. It does not identify the mean random
count, a relative error uniform in growing q, or a new moment threshold.
The original t>2 theorem and limiting coefficient remain unchanged.

Canonical declarations: retained_parameters_eq_layers,
effective_count_bounds, positive_exponential_lower, total_exponential_lower,
retained_start_density and uniform_density_approximation in
PaperP1.ValuationDensityBounds.

All 27 new theorems and their exact direct axiom audit passed under Lean
v4.36.0-rc2, with proof warnings as errors. Only propext, Classical.choice
and Quot.sound occur. Whole-project replay and manuscript integration are
pending.
