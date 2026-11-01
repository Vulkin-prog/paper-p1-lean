# Companion T19.5 — Quantified support of the original count

Source: Proposition T19.5, page 69, `p1:limits:effective-tail`,
`companion_sections/limits_appendix.tex:255`. Original statement SHA-256:
`8e2ed24d53e5de8afa77692efe805e5747c327d27dbb7f515bda212839f37676`.
The original source bytes are preserved.

`EffectiveSupport.companion_T19_5` proves both source conclusions for
the actual infinite prime-sign count. With H=log N, h=log H, the literal
threshold is ceil(sqrt(N) exp(K H/h^(2/3))). For every fixed D>0 and
integer r>=0, its truncated r-th moment is eventually <=N^(-D).
For every fixed eta>0 the same bound holds at N^(1/2+eta), which is
stronger than the source's big-O formulation.

One N threshold precedes every length in a prescribed critical band.
`EffectiveSupport.band_uniform_constant` proves that K can be chosen
before the band width C. Only the N threshold depends on C. In fact the
proof gives the explicit coefficient

    K = E + D + r + log 4,
    E = Cb*a + |log u| + log 3 + 1,
    a = 1 + u*(log 4 + 4),  u = 1/log 2 + 1,

where Cb is the internally proved prime-budget Rankin constant. This
band-independent coefficient and the removal of the bounded-pair-moment
dependency are recorded as P1-MATH-0034.

## Checked proof chain

1. `EffectiveTailScale` defines q=h^(2/3), t=h^(1/3), s=H/q and the
   literal integer k=ceil(q). It proves t*q=h, t^2=q and q<=k<=2q.
   Eventually h>=1, h^2<=H, h<=s, s>=1 and 2k<=sqrt(N). All real
   powers, positive denominators and the integer ceiling are included.
2. `EffectivePrimePool.raw_budget_le_envelope` bounds the actual pool
   after every j<=2q old windows by the logarithmic budget (a H t)^2.
   The already proved finite Rankin bound at sigma=1/2 gives the pool
   count <=exp(H/2+log(3)/2+Cb*a*s). No asymptotic estimate for the
   cardinality of a prime set is assumed.
3. `EffectiveOrderMoments.finite_exception_bound` combines this with
   the actual deterministic two-supported-value exception criterion.
   Its exceptional size is <=exp(H/2+E*s). Exact independence outside
   the set and event inclusion inside it supply the previously proved
   factorial recurrence.
4. `EffectiveOrderMoments.factorial_bound` proves
   F_j<=(2 exp(H/2+E*s))^j for every j<=ceil(q). The recurrence starts
   at F_0=1. The proof uses the exact critical marginal upper bound
   for Np, but does not use F_2=O(1) or any fixed-order moment theorem.
5. `EffectiveSupport.uniform_tail` applies the actual falling-factorial
   Markov inequality, after proving 2k<=the unrounded threshold. At
   the displayed K its probability is <=exp(-(D+r)H). The deterministic
   bound Z<=N then gives the truncated moment <=N^(-D).
6. The literal ceiling increases the threshold. The power-threshold
   comparison follows from q tending to infinity, with all fixed
   parameters chosen before N. It does not extrapolate a fixed-order
   constant or exchange the order of quantifiers.

## Scope

The estimate is for the original count, including irregular windows.
It supplies no bounded second moment or low-order asymptotic. T19.4's
stronger factorial bound retaining its bounded initial pair moment is
a separate result and is not counted complete here. No main Poisson
theorem, revised manuscript or Palomar registration is claimed.
