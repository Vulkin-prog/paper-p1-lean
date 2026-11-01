# Prime-support budgets for growing degree

This checkpoint proves the prime-support and enumeration ingredients used
in companion T5.2 (`p13:short:split`). It does not prove the full actual
split-product count. Coverage remains 56/167, with 54 confirmed mathematical
improvements. Formalizing an existing source ingredient adds no improvement
entry by itself.

## Exact finite arithmetic

`PrimeFactorialBudget.positive_factorial_le_prod` proves that a finite set
of positive distinct integers has product at least its cardinal factorial.
The proof removes the maximum and compares its cardinality with the actual
positive-integer interval. Applied to the actual prime factors of n>0,
whose product divides n, it gives omega(n)!<=n.

The already checked finite Stirling inequality gives

    omega(n)*(log(omega(n))-1) <= log n.

The zero-support case n=1 is included separately. A proved monotonicity
argument inverts this inequality: if t>0, log t>=1 and
log n<t(log t-1), then omega(n)<t.

For squarefree n, the exact factorization formula proves
card(divisors(n))=2^omega(n), including n=1. This is not inferred from an
estimate at fixed polynomial degree.

## Uniform growing-degree statement

For every fixed c>=0, C>=1, epsilon>0, there is one N0 before every N>=N0,
positive natural n and natural d such that

    d <= c loglog(N),    n <= (CN)^d.

Then omega(n)<=(c+epsilon)log N. The proof compares the finite factorial
budget with t=(c+epsilon)log N, using proved limits of elementary
logarithmic expressions. The degree is quantified after the threshold.

For every fixed real a>1, rescaling epsilon proves

    a^omega(n) <= N^(c log(a)+epsilon).

The exact squarefree-divisor budget is the a=2 case. The cardinality of
the actual function space from n.primeFactors to Fin k, k>=2, is k^omega(n),
and has the same bound at a=k. No count of all prime assignments is assumed.

## A fixed resultant-height error

For every fixed real E, the proof also accepts the explicit ordinary
height premise

    log n <= c loglog(N) log(CN) + E (loglog(N))^3.

The cubic error is proved negligible relative to log(N)loglog(N),
uniformly in the actual n. This gives the same prime-support and
exponential budgets. E may be negative; the bound remains valid.

This height premise is not yet derived for the paper's actual q*D_A.
The actual split-product resultant/parity bookkeeping, the restriction
of two selected linear kernels to rad(q*D_A), their derived height,
the selected quadratic enumeration and the full fixed-kernel count all
remain to be proved. T5.2 stays in progress.

No new unproved literature input, Paper C port, source-byte change or
Palomar registration is introduced.

Verification: full Lean v4.36.0-rc2 build passed (9,573 jobs), the actual
audit passed for all 3,927 declarations using only the three permitted
kernel axioms, and 1,642 distinct ledger/finding names were checked.
