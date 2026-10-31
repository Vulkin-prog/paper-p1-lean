# Fixed-source product certificates — companion T4.2

**Status: proved in full.** Source: companion V1.6, page 27,
`companion_sections/fixed_moments.tex:68`, label `p1:fixed:CRT`.
Exact statement SHA-256:
`ec46fac6ac93bd36c65662a7da8b884193199f09a5edb6898bfd7559a7b43722`.

## Literal source population and offsets

For actual source centres x_a in [N,2N), the value at offset index u in
Fin(L+1) is x_a-1+u. This retains B=L+1 and both endpoint offsets.
`exists_offset_index`, `offset_value` and `offset_dvd_iff` prove the exact
dictionary with every signed integer offset in [-1,L-1], including natural
and integer divisibility. No negative-offset convention is left implicit.

`FixedSourceCertificate.HasIntegerCertificate` is the literal predicate:
each G_i>1 divides one actual signed-offset source value; the modules are
pairwise coprime, their product exceeds N, and each divides one actual
signed-offset target value. `hasIntegerCertificate_iff` identifies it with
the natural offset-index version. `mem_sourceTargets_integer` proves that
the finite source population is exactly the original set of centres.

The larger `certificateTargets` population permits product(G_i)>=N.
`mem_certificateTargets` proves its complete witness description, and the
original strict population is proved contained in it.

## Finite code count and uniqueness

For a generic finite source family v, form the union of its actual divisor
sets, keeping divisors greater than one. A code chooses k pairs consisting
of one such divisor and a target offset among B possibilities. The number
of all codes is at most

`(B * sum_a tau(v_a))^k`.

Every valid certificate is encoded: `ProductCertificate.mem_targets`
proves the full witness equivalence. The source value witnessing a chosen
divisor need not be retained in the code. Counting the union of possible
divisors only reduces the alphabet, and the proved union bound controls it.

Two targets with the same code are congruent modulo every chosen module.
The finite lcm equals their product by coprimality and divides both natural
differences. Each difference is smaller than the interval length N; if the
product is at least N it must be zero. `ShortIntervalCongruences` proves
this for every half-open interval [U,U+N), U>=1. Thus each valid code has at
most one target. `ProductCertificate.card_targets_le` proves the count,
without an assumed CRT output or uniqueness premise.

## Uniform N^epsilon bound

For sufficiently large N, the upper logarithmic width bound
B<=D*logN implies L<=N. Every actual source value is positive and at most
N^2. The already proved divisor estimate, with its threshold before every
integer in that polynomial box, gives tau(v_a)<=N^eta uniformly, where
eta=epsilon/(2k). The finite code count becomes

`s^k * B^(2k) * N^(epsilon/2)`.

The proved logarithmic-width subpolynomial bound absorbs its fixed
s^k*B^(2k) factor into N^(epsilon/2). Real-power identities give the final
N^epsilon. `certificateTargets_le_power_eventually` chooses one threshold
before N,L and every source tuple, using only the upper width condition.

`critical_band_scale` supplies that upper ceiling for every length in the
literal band |L-log(N)/log(2)|<=C. The stronger
`critical_band_certificateTargets` retains the relaxed product threshold;
`companion_T4_2` gives the exact original strict population for fixed s,k>=1.
No relation condition or fixed advance choice of G_i is imposed on the
population: all certificates are counted.

## Improvement, inputs and validation

`P1-MATH-0018` records product(G_i)>=N and the upper-width condition alone.
The original strict conclusion is preserved. No error or optimality claim
is made. The proof also gives the explicit finite code bound, avoiding a
separate ordered-factorization count for the module product.

Mathlib at `9d581dfff2e41de989072ea63abf3daf69311520` supplies natural
divisors, finite lcm/product identities, finite function counts and power
algebra. Existing attributed P1 divisor and logarithmic-growth proofs are
reused; no additional Paper C source is ported. All congruence, finite count
and eventual estimates are proved internally.

The full Lean v4.36.0-rc2 build passed (8,835 jobs). The actual axiom audit
passed for all 2,008 project theorem/lemma declarations, with only
`propext`, `Classical.choice` and `Quot.sound`. Coverage is 30 / 167:
11 main results and 19 companion results. No Palomar registration is made.

All 297 distinct coverage/finding declaration names were checked directly by Lean.

Validated implementation of companion T4.2 and P1-MATH-0018:
[ed4ed43ecc05c2f7823ba9b0acca98bc1f62fc5d](https://github.com/Vulkin-prog/paper-p1-lean/commit/ed4ed43ecc05c2f7823ba9b0acca98bc1f62fc5d).
