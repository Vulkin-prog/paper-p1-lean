# The small-prime coefficient budget — companion T2.1

**Status: proved.** Source: companion V1.6, page 20,
`companion_sections/supplemental_arithmetic.tex:19`, label
`p1:arith:smallpart-budget`. Exact statement SHA-256:
`22145d7cf62fc668f06d7706f77e8d12bc0c98008d24235ca536504f8f46ff2c`.

## Exact small odd-prime part

`smallOddPart B n` is the product of precisely the primes at most B
occurring to odd valuation in n. The existing `largeOddKernel B n`
is the product over the complementary large primes. `small_mul_large`
and `smallOddPart_eq_div` identify the new quantity with the source's
sf(n)/K_B(n). `squarefreeKernel_mul_squarePart` identifies its complete
odd-prime kernel with the canonical square-times-kernel decomposition.
All these prime products are positive. Their real logarithms are ordinary
finite sums, rather than a surrogate counting function.

## Uniformity in every translated interval

`IntervalMultiples.card_multiples_interval_le` proves that the number of
multiples of p in [U,U+B) is at most floor(B/p)+1. Its proof subtracts
the least such multiple and divides by p, giving an injective encoding
into the literal finite range. No bound on U enters the estimate.

Dropping the odd-valuation condition bounds the logarithmic sum by this
multiple count. `div_le_factorization_factorial` proves floor(B/p) is
at most the p-valuation of B!, by counting its individual factors. The
exact factorization logarithm then gives the source's finite estimate:

`sum_(U≤n<U+B) log(u_B(n)) ≤ log(B!)+sum_(p≤B) log p`.

The proved elementary library bound `primorial B≤4^B` yields the explicit
absolute remainder B log 4. Together with B!≤B^B this proves

`sum_(U≤n<U+B) log(u_B(n)) ≤ B log B+(log 4)B`.

`card_largeSmallPartValues_le` bounds the exact finite set where u_B(n)>B^A.
For every B≥2 and A>0 it gives

`card ≤ (1/A+((log 4)/A)/log B)B`.

Thus one absolute constant works for all translated positive intervals,
and the final remainder has exactly the source's O_A(1/log B) dependence.
`companion_T2_1` packages both conclusions. There is no asymptotic cutoff,
critical-band condition or external arithmetic estimate among its premises.

## Inputs and validation

The proof uses internal prime-parity definitions and finite sums, and
proved Mathlib facts at commit `9d581dfff2e41de989072ea63abf3daf69311520`:
`Nat.card_multiples`, `Nat.factorization_prod_apply`,
`Nat.Prime.dvd_factorial`, `Real.log_nat_eq_sum_factorization`, and
`primorial_le_four_pow`. It uses no prime number theorem and ports no
additional Paper C proof.

The full Lean v4.36.0-rc2 build passed (8,749 jobs), followed by the actual
axiom audit of all 1,746 project theorem/lemma declarations. Only `propext`,
`Classical.choice` and `Quot.sound` occur. Coverage is 22 / 167 numbered
results: 9 main and 13 companion. No new mathematical correction or
improvement is identified, and no Palomar registration is made.
