# Exact bivariate law of the Poisson reference field

Checkpoint P1-MATH-0997 describes the full law of two reference counts.
It applies to every independent realization, arbitrary finite packets,
overlapping observations and zero rates. For pair packets it includes
both distinct sites and the diagonal case.

```text
(Z_x,Z_y) has the law of (U+W,V+W),
U ~ Poisson(p_x-r), V ~ Poisson(p_y-r), W ~ Poisson(r), independently.
r = Cov(Z_x,Z_y), 0 <= r <= min(p_x,p_y).
```

For pair packets, r is p_x when x=y, the retained pair rate when the
distinct pair is retained, and zero otherwise. These parameters describe
the reference construction. The arithmetic approximation keeps its
original exponent and fixed-degree quantifier order.

For a=p_x-r, b=p_y-r, c=r and every m,n in the natural numbers,

```text
P(Z_x=m,Z_y=n) = exp(-(a+b+c)) *
  sum_{k=0}^{min(m,n)} a^(m-k)*b^(n-k)*c^k / ((m-k)!*(n-k)!*k!).
```

The proof identifies the finite preimage of the addition map, computes
the independent product masses and factors their exponential. No
interchange of infinite sums is needed. Zero intensities use the usual
natural-power convention, including 0^0=1. In particular the joint zero
probability is exp(-(a+b+c)).

Twenty-one theorems and four definitions passed strict Lean v4.36.0-rc2 prototype compilation; exact direct axiom checks of all twenty-one theorems permit only propext, Classical.choice and Quot.sound. Root replay and manuscript integration are pending.
