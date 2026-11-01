# Exact independence after old raw-window observations

Target: companion Proposition T1.15, page 17, `p1:arith:fixed-branching`,
`companion_sections/arithmetic_appendix.tex:1075`.
Original statement SHA-256:
`a92935eea4e5bf50e484074d857575c10136d376340ccbfe4cc24180ff9d3f97`.

Status at this checkpoint: **in progress**. The original consecutive
windows, full relative-vector law, independence from every old raw value,
literal rounded exceptional-set bound and uniform fixed-j exponent are
proved. The final extension to fixed dilations, subsets and fixed enlarged
logarithmic windows is not yet counted as complete numbered coverage.

## The full vector, rather than one start indicator

`ConditionalRelativeBits` defines the actual infinite old raw-bit vector
and conditions every possible new relative word on its realizable old
observation. Its old-event probability is proved positive. The exact
conditional law is derived from the already proved affine quotient-kernel
calculation, with no probability bound as an input.

When the new window contains at most one value supported on the old
prime pool, the relative kernel is zero. Every new word then has
conditional probability 2^(-L). For unrealizable old vectors both the
old event and every joint event have zero mass. These two cases prove
the literal joint pushforward equals the product of the fair relative
cube and the actual old-vector law. Projection gives the fair marginal,
and `independent_of_old` proves Mathlib's `IndepFun` for the entire new
vector and all old raw observations under the original infinite measure.

## Literal finite exceptional bound

`PrimeSetEuler` proves the reciprocal-half-power sum is at most twice
the square root of the number of positive distinct integers. Removing
the largest element and telescoping the square root supplies a direct
finite proof. It yields the exact Euler factor exp(2*sqrt(card(pool))).

`OldPrimeCardinality` separates small primes from the actual large old
prime divisors. Their total logarithmic budget proves

    card(pool) <= ceil(pi(B) + j*B*log(3N)/log B) = m_{j,N}.

No prime-number estimate is assumed in this finite bound. The inclusive
pi(B), integer ceiling, literal B=L+1 and all old-value choices are kept.

`BranchingExceptional.badStarts` consists solely of windows with at least
two old-pool-supported values. Every other window has the full independence
property, including contacts that satisfy this criterion. The deterministic
incidence budget gives

    2*card(badStarts) <= B*card(poolValues).

Thus `badStarts_card_explicit` gives

    card(badStarts) <= (B/2)*sqrt(3N)*exp(2*sqrt(m_{j,N})).

This stronger bound omits a separate j*(2L+1) contact term and halves
the pool coefficient. It implies the original source bound exactly.
P1-MATH-0030 records the improved finite exceptional set, restricted to
the proved original-window scope at this checkpoint. It asserts no
optimality or bound on every kind of arithmetic dependence.

## Uniform fixed-j size

The already proved actual prime-pool count and the logarithmic critical
width give card(badStarts)<=N^(1/2+epsilon), with a threshold before all
old starts and all lengths in the fixed critical band. Old sets of
cardinality at most j include repeated entries in a j-source list.

`FixedWindowBranching.original_windows_critical` combines this exponent,
the original literal finite bound, the fair full vector law, `IndepFun`
and every conditional word probability. Its exceptional set is constructed
from integer factorizations and is independent of the random signs.

All proofs are new P1 code using the validated model. No further Paper C
source or unproved external mathematical statement is introduced. The
earlier reciprocal-sqrt helper remains attributed to its recorded port.

## Original-window checkpoint validation

The full Lean v4.36.0-rc2 build passed (9,071 jobs). The actual axiom
audit passed for all 2,713 theorem/lemma declarations, allowing only
`propext`, `Classical.choice` and `Quot.sound`. All 618 distinct coverage
and finding names were checked directly by Lean. Original source bytes
and all 167 numbered statement hashes are preserved. Coverage remains
41 / 167 while the final generalized-window clause of T1.15 is open.
There are 30 confirmed improvements. No Palomar registration is made.
Available Ubuntu-root space is 17.89 GiB.
