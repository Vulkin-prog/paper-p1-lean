# Effective finite-depth valuation bounds

Checkpoint P1-MATH-0989 strengthens the finite construction for companion T19.7.
All original and revised numbered statement blocks are preserved.

For a prime q<=N, put m=floor(N/q). In the retained multiplier interval
[m+1,2*m), layer j consists of multiples of q^(2*j) that are not multiples
of q^(2*j+1). Every such multiplier has even valuation and belongs to the
actual retained set. These layers are pairwise disjoint.

The exact translated-interval multiple count is
floor((U+B-1)/d)-floor((U-1)/d), for U>=1. In real form it differs from
B/d by at most one. The resulting endpoint estimate, with the zero layer
treated by its sharper earlier count, gives for every finite depth k>=0

```text
B_k = N/(q+1) * (1 - (1/q)^(2*k)) - 3*k
    <= ValuationPrimeCylinder.starts(N,q).card.
```

The finite geometric sum is exact. Its inclusion in the actual retained
set is proved before taking the cardinality bound. The image map u->q*u+1
is injective, so multiplier and start counts agree.

For every prime q<=N, t>=0 and finite k, both full actual exponential
moments are at least exp(t*B_k-primeCount(M)*log(2)), where
M=2*q*floor(N/q)<=2*N. The supported cylinder and integrability/monotonicity
transport are the already proved actual prime-sign constructions. No
abstract moment-generating function or target count is supplied as input.

Depth zero gives zero. Depth one is exactly N/q-N/q^2-3. At the original
critical scale q=17 and N=2^(q-1), depth two gives a strictly greater budget
and a strictly stronger exponential lower bound for every t>0 at the same
cylinder cost. Larger depths need not improve this explicit estimate:
the endpoint error grows as 3*k. The parameter k is valuation-layer depth,
not moment order. No infinite sharp density or improved t threshold is claimed.

Canonical declarations: finite_geometric_lower, positive_exponential_lower,
total_exponential_lower and strict_budget_gain_on_original_scale in
PaperP1.ValuationLayerCounts.

Full Lean v4.36.0-rc2 replay passed at source f55fe63b9538863bd0ec8bdf8b3deacb70f49e4d: 18,573 build jobs, 19,540 source-discovered theorem axiom checks and 19,692 distinct declaration-reference checks, all actual process exits 0. Proof warnings are errors; only propext, Classical.choice and Quot.sound occur.

The full replay and original compressed logs are preserved in [the validation record](validation/checkpoint-0989/validation.json).

This refinement is integrated in the unnumbered version 1.7 companion appendix, under Exact valuations and finite layers. The 65-page article and 101-page companion were rebuilt and reviewed; all 167 numbered statement blocks are preserved. See [the manuscript validation](manuscript-v1.7-validation.json).
