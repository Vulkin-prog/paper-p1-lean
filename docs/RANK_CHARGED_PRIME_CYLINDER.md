# Charge the effective rank of the actual forcing event

Checkpoint P1-MATH-0991 strengthens the finite construction for companion
T19.7. All 167 original and revised numbered statement blocks are preserved.

Let G be the complete even-valuation retained start set, C=G.card,
L=q-1 and M=2*q*floor(N/q). The actual finite prime-sign vector is sigma.
Define one linear system with rows indexed by G times Option(Fin L):

```text
none:    valueBit(sigma,x-1) = 1,
some j:  valueBit(sigma,x+j) = 0,   0<=j<L.
```

For L>0 these equations are equivalent to every selected start having
negative predecessor and a positive word of length at least L. Their
solution forces the restricted positive count to equal C. The existing
one-negative-prime sample proves compatibility for the actual G, q and M.

The exact mass of this affine fiber is 2^(-r), where r is its effective
linear rank. Rank-nullity proves r<=primeCount(M). For every t>=0,
both full actual exponential moments are therefore at least

```text
exp(t*C - r*log(2)).
```

The proved finite-layer budgets B_k and the explicit logarithmic-depth
budget L(N,q) may each replace C in this expression. The argument first
bounds the restricted finite expectation, then identifies its infinite
cylinder integral and compares it to the full count. The compatible mass
is derived internally; it is not a supplied probability or count premise.

Any prime below M that divides none of the observed predecessors and word
values supplies a nonzero homogeneous kernel vector: flip just that prime
bit. Rank-nullity then gives r<primeCount(M), proving at least a factor-two
gain over the single-atom lower bound with exactly the same count C.

At N=18,q=3, the retained multipliers are exactly 7,8,9,10,11 and the
five starts are 22,25,28,31,34. Their observed integers lie between 21 and
35. The supported cutoff is 36, with eleven primes. Prime 19 divides no
observed integer, so r<=10. Both full moments have the numerical bound

```text
exp(5*t - 10*log(2)) = exp(5*t)/1024,   t>=0,
```

compared to exp(5*t)/2048 from the previous same-count atom bound. This
does not assert that ten is the exact rank, a general explicit rank
formula, or an improved asymptotic threshold. The original t>2 theorem
and its limiting coefficient remain unchanged.

Canonical declarations: retained_forcing_mass, positive_exponential_card_lower,
total_exponential_card_lower, rank_lt_primeCount_of_unused,
positive_explicit_example and total_explicit_example in
PaperP1.RankChargedPrimeCylinder.

All 31 new theorems and their exact direct axiom audit passed under Lean
v4.36.0-rc2 with proof warnings as errors. Only propext, Classical.choice
and Quot.sound occur. Whole-project replay and manuscript integration are
pending.
