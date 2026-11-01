# Exact independence after old raw-window observations

Target: companion Proposition T1.15, page 17, `p1:arith:fixed-branching`,
`companion_sections/arithmetic_appendix.tex:1075`.
Original statement SHA-256:
`a92935eea4e5bf50e484074d857575c10136d376340ccbfe4cc24180ff9d3f97`.

Status: **proved**, including original consecutive windows, the full
relative-vector law, independence from every old raw value, the literal
rounded exceptional-set bound, the uniform fixed-j exponent and all
fixed-dilation, subset and enlarged logarithmic-window extensions. The
earlier original-window checkpoint is preserved below.

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

## Earlier original-window checkpoint validation

The full Lean v4.36.0-rc2 build passed (9,071 jobs). The actual axiom
audit passed for all 2,713 theorem/lemma declarations, allowing only
`propext`, `Classical.choice` and `Quot.sound`. All 618 distinct coverage
and finding names were checked directly by Lean. Original source bytes
and all 167 numbered statement hashes are preserved. Coverage remains
41 / 167 at that earlier checkpoint, when the generalized-window clause
was still open.
There are 30 confirmed improvements. No Palomar registration is made.
Available Ubuntu-root space is 17.89 GiB.

Validated original-window branching implementation and P1-MATH-0030:
[8b5542412a96f221e87921abc9892ddabdac0505](https://github.com/Vulkin-prog/paper-p1-lean/commit/8b5542412a96f221e87921abc9892ddabdac0505).

## Arbitrary injective selections and dilations

`SelectedBoundary.evenExtend` embeds any selected even word into the
complete enclosing boundary. The row embedding is injective whenever
the selected coordinate list is injective. `DotTranspose` proves its
transpose has no row relations, and `FairBinaryCube` proves the exact
fair-cube pushforward. No rank or uniform-output law is assumed.

`SelectedRelativeBits.selectedBits_apply` identifies these outputs with
the literal sums of the actual bits at the selected integer arguments.
The complete-boundary identity proves they are measurable functions of
the original enclosing relative vector. They retain the fair law under
injective selection and independence from every old observation. Old
observation subsets are handled by restriction. Empty relative vectors
and all repeated old observation values are included.

`BranchingPatterns.dilationIndices` constructs the injective coordinate
map i -> a+d*i for every positive integer d fitting the enclosing
diameter. `dilation_label` proves the actual integer label is
x-1+a+d*i. Thus the generalized result concerns actual fixed dilations,
in addition to arbitrary injective subsets, rather than an abstract
assumed preservation of their laws.

## Enlarged widths, bounded heights and changes of center

`BoundedObservationPool` treats any finite old-value set R with at most
j*B members in [1,3N], with B<=D*log N for fixed D>=0. The actual prime
pool again has a proved logarithmic-square budget. The finite Euler
inequality gives its N^(1/2+epsilon) count uniformly before every old
observation and width choice.

`GeneralBranchingExceptions` constructs the same two-supported-value
exception set on **any** bounded finite set of enclosing windows. Its
half-incidence bound and exact independence apply uniformly to every
injective subset of each retained window. `GeneralWindowBranching`
absorbs any fixed positive height multiple K*N and every fixed enlarged
logarithmic diameter into the threshold. It requires only that all used
integers are positive and that enclosing starts are at least two, which
the source's fixed positive comparable-height condition gives eventually.

`GeneralBranchingTheorem.reindexed_windows` pulls back the exceptions
through any injective deterministic center map, with no cardinality
loss. It allows the selected coordinate pattern to vary deterministically
at every center, with one common exceptional set. Actual old blocks are
encoded by `BranchingPatterns.observationValues`; their j*B cardinality
bound is proved from their index set, including repeated values.

`companion_T1_15` bundles the literal original-window statement with this
generalized clause. One threshold precedes every length, source choice,
old raw vector, selected subset, fitted fixed dilation and injective
center change. No exception count, conditional law, independence,
rank, Euler or prime-pool estimate is an input. No additional Paper C
port or unproved external mathematical statement is introduced.

## Complete-result validation

The full Lean v4.36.0-rc2 build passed (9,089 jobs). The actual axiom
audit passed for all 2,759 theorem/lemma declarations, allowing only
`propext`, `Classical.choice` and `Quot.sound`. All 635 distinct coverage
and finding names were checked directly by Lean. Source checks passed
for 138 manifest entries and all 167 original statement hashes.
Numbered coverage is now 42 / 167: main 15 / 73, companion 27 / 94.
The 30 confirmed improvements retain their earlier validation records.
Original manuscript bytes are preserved and no Palomar registration
is made. Available Ubuntu-root space is 17.86 GiB.

Validated complete implementation of companion T1.15:
[aa40b4a69208172c6fca0cdd9def2e336e92f278](https://github.com/Vulkin-prog/paper-p1-lean/commit/aa40b4a69208172c6fca0cdd9def2e336e92f278).
