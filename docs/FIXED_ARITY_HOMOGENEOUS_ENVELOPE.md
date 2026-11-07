# Common fixed-arity mass bound

Checkpoint P1-MATH-1004 supplies one proof for four weights already used in
article 15.5 and the discussion preceding companion T8.2. The actual homogeneous
mass is included, even when an original affine marginal vanishes.

Write `q0(I)` for the probability of the genuine homogeneous event on the true
windows, `p=2^-L`, and `rho(I)` for their effective relative nullity. The exact
factorization and the uniform local rank bound give

```text
q0(I) = product_x q0({x}) * 2^rho(I)
q0({x}) <= 2p
q0(I) <= 2^|I| * p^|I| * 2^rho(I).
```

This finite comparison uses homogeneous local probabilities, not the original
affine marginals `p_x`. No regularity or affine compatibility is imposed.
The existing nominal estimates then give, for every fixed `r>=3`,

- total homogeneous mass at most `N^(-r/2+epsilon)`;
- dense homogeneous mass at most `N^(1-r+epsilon)` when `rho(I)>=eta L`;
- at most `N^epsilon` dense hosts.

The constant `2^r` is absorbed by spending half the exponent margin, after
fixing `r,C,eta,epsilon`. The common scale threshold precedes `N,L` and every
deterministic subfamily being summed. This gives no estimate with growing `r`.

The original heterogeneous rank weight, actual joint probability and absolute
centered coefficient are each bounded by `q0(I)` on a nonempty family. Thus
`uniform_all_bounds` gives all four mass estimates with the same threshold,
including locally deficient windows and zero original marginals. Its premises
contain the population conditions, never the target mass estimate.

The seven proved interfaces are in
[FixedArityHomogeneousMass.lean](../PaperP1/Asymptotics/FixedArityHomogeneousMass.lean):
`point_le_nominal`, `mass_le_nominal`, `uniform_nominal_cap`,
`finite_original_domination`, `uniform_mass`, `uniform_dense_mass`, and
`uniform_all_bounds`.

The complete pinned build, axiom audit and reference replay are recorded in
[checkpoint 1004](validation/checkpoint-1004/validation.json). The separate
review instance also read all seven bodies and actual compiled types in its
[frozen report](reviews/2026-11-07/fixed-arity-envelope.json). That is an
AI-assisted scope review, not human certification.

For editing, this supports a shared comparison paragraph near T8 and a short
reference from article 15.5. The arithmetic dense-host argument, all numbered
statements and the distinct compressed-family proof must remain available.
All frozen manuscript sources and PDFs are preserved. No Palomar submission
is launched by this checkpoint.
