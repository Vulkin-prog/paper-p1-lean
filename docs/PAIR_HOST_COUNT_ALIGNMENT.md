# Main 3.2 — Stronger full-loss support count and exact independent mass

Source: Proposition 3.2, page 15, `p1:arith:hosts`,
`main_sections/arithmetic.tex:98`, statement SHA-256
`65da7e8acfacc0a5bc2c351934c0e44e09d3fc6068a8862c300b6eeaeee8c5fe`.
This result remains **in progress**: the first displayed count is now
proved with a stronger exponent, while the separate weighted nonaligned
residual remains open. Numbered coverage stays 68/167.

## Full source loss, including local kernels

`PairHostCover.hosts` is the literal finite set of all ordered dyadic
pairs with positive full loss

    rho(x,y)=2L-finrank(S_x+S_y).

It includes equal centres and contacts. `separatedHosts` imposes the
source strict separation. The proof does not replace full rho by the
relative intersection rank on locally deficient windows.

For two regular coordinates, the submodule dimension identity proves
that full loss equals the intersection dimension. Consequently a host
with both coordinates regular lies in the actual effective pair set of
main 10.3. Every other host belongs to one of the two products

    irregularStarts x dyadicBlock,   dyadicBlock x irregularStarts.

`PairHostCover.cover` and `card_bound` prove this actual cover and its
finite cardinal inequality.

## Stronger uniform count

`OriginalPairHosts.effective_hosts` instantiates complete main 10.3
with the actual complete value intervals. The proved geometry supplies
their fixed comparable positive heights and signed-distance radius.
The proved regular-set estimate counts every local exception by N^eta.
Thus, for every fixed critical band and epsilon>0, one N threshold
precedes every length and gives

    card(hosts) <= N^(1+epsilon).

The two contributions and their factor three are absorbed with internal
margin epsilon/2. The result holds before separation. `improved_support`
restricts it to the source set, and `article_3_2_support` implies the
printed exponent 6/5+epsilon. This improvement is P1-MATH-0068. It uses
the completed, acyclic half-count and regular-set proof chains; the
unfinished weighted pair theorem is not an input.

## Exact heterogeneous independent mass

`PairHostIndependentMass.mass` sums the actual products p_x*p_y over
this full host set. The proved uniform marginal cap and finite product
bound give

    mass <= N^(-1+epsilon).

Both actual heterogeneous marginals are retained. This is an independent
weight bound; it does not estimate the joint activation mass, the
covariance sum or the separate weighted sum of 2^rho-1.

## Progress on the original second factorial moment

`PairHostMoment.finite_second_bound` proves the exact finite inequality

    F_2 <= N^2 p^2 + card(hosts)*M

for any nonnegative bound M on all actual marginals. Ordered distinct
tuples map injectively to their physical pairs. Outside the full-loss
host set, the actual spaces have full local rank and are direct, so their
joint probability is at most p^2. Inside it, event inclusion bounds the
joint probability by an actual local marginal. No compatibility or
independence is assumed for those hosts.

`SecondMomentSubpower.uniform_subpower` combines this inequality, the
improved count and the exact marginal cap to prove, for every fixed
epsilon>0, uniformly over the critical band,

    F_2 <= N^epsilon.

This is progress on T19.4. It does not prove F_2=O(1), and a separate
fixed-epsilon threshold cannot be substituted into a growing-order
estimate. T19.4 remains in progress. No new external assumption, Paper C
port, manuscript edit or Palomar registration is introduced.

Pair-host verification: Lean v4.36.0-rc2 full build passed (9915 jobs); actual axiom audit passed for all 4729 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 2444 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 16.69 GiB. The stronger full-loss host count and exact heterogeneous independent mass are proved; main 3.2 remains in progress for its weighted nonaligned residual. The actual F_2<=N^epsilon bound does not close T19.4. Coverage stays 68/167; confirmed improvements are 68. No target host count, external assumption, Paper C port, manuscript-byte change or Palomar registration.
