# Conditional full-support half-count — main Theorem 10.1 complete

The entire simultaneous induction, actual stage counts and final effective-
block statement are proved. The final declaration is
`PaperP1.ValueHeightHalfCount.article_10_1`, aligned with main 10.1,
`main_sections/half_counts.tex:21`, and the iteration in
`companion_sections/half_counts.tex:157`. No target count is an input.

## Literal source objects and quantifiers

`EffectiveWindowLists.lists` consists of injective ordered lists of r new
natural centres. Each new block is an arbitrary finite set of actual
natural values, with repetitions already merged. A witness chooses a
vector in that block's effective even-selection image, nonzero in its own
absolute square-class space. The total is in the full linear span of all
values in s fixed old blocks. There is no nonzero-modulo-old restriction.
Old blocks can overlap, be dependent or be empty. New centres can equal
old centres; only the new list is required to be injective.

The final threshold precedes N, the critical length L, every finite
candidate-centre set, all old centre positions, every old block and all
new block families. The explicit source geometric hypotheses are:

- every actual value is in a fixed positive comparable interval [aN,bN];
- its signed distance from the relevant centre is at most D*(L+1);
- L is in an arbitrary fixed band around log(N)/log(2).

For every fixed r,s,a,b,D,band and positive epsilon, the eventual count is
at most N^(r/2+epsilon). This implies the printed fixed-constant O bound.
The proof even permits r=0 and D=0. It imposes no size or interval condition
on the finite candidate-centre set itself.

`BlockCentreHeights` proves that an actual value in a nonempty block
forces its centre into [min(a/2,1)N,max(b+1,1)N] eventually. A nonzero
effective vector ensures that the new block is nonempty. Empty old blocks
can be recentered at N without changing any value or their full span.
Thus comparable centre heights are deduced from the source value heights.
They are not an additional source hypothesis. The radius
ceil(D*(L+1))+1 is positive and uniformly logarithmic in N.

## Exact effective-image and old-span bridges

`EffectiveWindowLists.even_space_selection` represents every effective
vector by an actual even subset of distinct values. `lift_selection`
transports that subset to integer offsets v-x, preserving its cardinality
and its parity-vector sum. Positivity on the full bounded window verifies
the inverse value identity. `subset_window_lists` then embeds actual
effective lists in the counted offset-witness lists.

Every remaining projection stays nonzero in its own space after deleting
a coordinate. Adjoining the deleted full value block to the old sources
preserves the remaining total by submodule subtraction. Deleting two
coordinates iterates that exact identity. An actual tuple is determined
by its fixed coordinate and restriction, or by its fixed pair and
restriction. Hence the corresponding fibres inject into actual lists
with fewer targets and one or two additional old sources. The old span
is enlarged by full blocks, with no parity restriction on old selections.

The final arbitrary-old-source theorem first enlarges the centre set to
include the fixed old centres. Every threshold is chosen before these
positions. No independence, disjointness or separation premise is added.

## Actual classes and complete arithmetic inputs

Complete 9.2 counts every list admitting a witness with all motif sizes
at most a fixed m. Its eventual degree inclusion, old-generator count,
nonempty even selections and literal product/parity identity are proved.
For all other lists, `ChosenWindowWitness.chosen` fixes one actual witness
without enumerating possible witnesses. It has a long selection.

The initial actual exceptional set uses H=0. The identity K_0=sf and the
full T6.1 bound give at most N^(1/2+eta) exceptional centres. Outside it,
every distinct pair of bounded offsets has kernel product above N^(1/2).
This is the strict complement of the actual exceptional-set predicate.

`HalfCountStages.survivors` recursively filters actual lists. At step j,
it removes every tuple with a long chosen motif having at least t actual
kernels K_Y above N^(1/5). Full T6.3 projected control gives an actual new
or old receiver. The exact sum after deleting the source is the projected
relation supplied to that theorem. Its full old-span representation and
both directed degree counts have already been proved.

`CertificatePairs` counts actual directed source-receiver pairs.
`HalfCountCertificateLists` and `HalfCountStageBounds` apply the exact
one-/two-coordinate injections to actual new/old receiver classes. After
removing saturated tuples, complete constant-selection T6.2 places every
surviving long source in the actual deterministic smooth-modulus exception.
`HalfCountStageConfinement` proves that invariant on the actual survivors.

## Genuine simultaneous induction and exponent budget

`ConditionalHalfCount.uniform_count` is proved by strong induction in the
number of new targets, simultaneously for every fixed number of old sources.
For r+1 targets it actually invokes the proved lower-order estimates for r
targets with s+1 old sources and, when needed, r-1 targets with s+2 sources.
These are fewer new targets. The empty-target base is at most one.
The intermediate finite count interfaces are all instantiated here.

Set t=5*(r+s)+1 and m=t+25. This constant cap is eventually included in
the complete 9.2 range. Every long selection then has at least t+26 terms,
exactly the proved T6.2 requirement. No growing cutoff is needed in this
iteration, and no condition H>diameter is needed for the initial exception.

Choose eta=epsilon/16 and an integer J>0 with 1/(2J)<epsilon/8. The actual
schedule is x_j=j/(2J), with x_0=0 and x_J=1/2 exactly. At stage j<J use
A_j=2J/(j+1)>=2. There are finitely many fixed cutoffs; their thresholds
are combined before N, positions or block selections are supplied.

A new receiver costs a source pool N^(1-x_j+eta), an actual outgoing degree
N^(x_(j+1)+eta), and the actual r-1-target count. The total exponent is
(r+1)/2+1/(2J)+3eta. An old receiver is fixed, so the incoming degree and
r-target count cost at most (r+1)/2+2eta. At the final stage, a long source
lies in an actual N^(1/2+eta) set and the r-target count again gives
(r+1)/2+2eta. The one-target case has no new receiver and is included.

`FiniteStageCounts` telescopes the actual finite differences exactly.
`HalfCountPowerBounds.finite_assembly` sums the all-short class, initial
exception, all removed classes and final survivors, including every role.
The fixed factor is
1+2*(r+1)+J*((r+1)*r+(r+1)*s). All class exponents are below the target
plus epsilon/2; the proved fixed-factor absorption uses the remaining
margin. There is no accumulation of stage exponents and no assumed
asymptotic local count.

## Mathematical change and verification

P1-MATH-0064 records the constant selection-size threshold, full squarefree
initial exception, exact finite schedule and explicit value-height bridge.
Original manuscript bytes remain unchanged. No new Paper C port or external
unproved input is used. Palomar registrations remain a later milestone for
the completed development as a whole.

Coverage is now 63/167 (main 20/73, companion 43/94), with 64 confirmed
improvements.

Lean v4.36.0-rc2 full build passed (9,797 jobs); actual axiom audit passed for all 4,453 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 2,168 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 17.24 GiB. No unproved local or target count, new literature input, new Paper C port, manuscript-byte change or Palomar registration.

Proof checkpoint: [4b6397f3dda595939efcf044b2459e6945983df2](https://github.com/Vulkin-prog/paper-p1-lean/commit/4b6397f3dda595939efcf044b2459e6945983df2).
