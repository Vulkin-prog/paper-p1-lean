# Complete short projections into an old space — article 9.2

Corollary 9.2 is proved for actual ordered centre lists and actual nonempty
even integer selections. Coverage is 59/167 (main 19/73, companion 40/94).
The final source declaration is `ShortOldSpaceProjection.article_9_2`.
The stronger core is `uniform_projected_lists`, with the literal list
predicate identified by `ShortProjectedLists.mem_lists_iff` and
`mem_lists_of_even_nonempty`.

## Exact old space and positive density

`OldSpaceProjection.oldSpace O` is the full span of the parity vectors of
all values in O. It is not the smaller even-selection image. Its image
under the actual finite-cylinder parity pairing preserves membership of
every supported new sum; the cutoff is constructed to contain every old
and new value. The character image has cardinality at most 2^|O|.

For every finite effective old character space V, Phi_V=sum_{u in V}chi_u
is proved nonnegative, of mean one, and

    E Phi_V^p = |V|^(p-1),
    (E Phi_V^p)^(1/p) = |V|^(1-1/p)  for every p>0.

Orthogonality proves that E(Phi_V*product_i X_i) is exactly the projected
tuple count, including repeated centres. Every surviving term is one;
the unique old cancellation is built into the proved density identity.

## The full Holder and actual norm argument

A finite weighted Holder inequality with arbitrarily many factors is
proved using Mathlib's ENNReal integral theorem and finite sums. All zero
cases are included. At 1/a+r/v=1, its old-density cost is at most

    (2^|O|)^(r/v).

Actual finite-cylinder moment roots are proved equal to the unrestricted
split-sum lpNorm. Proposition 9.1 supplies these actual norms. A sufficiently
large fixed even v makes the old-density cost <=N^(epsilon/2) at
|O|<=E*logN, and the positive c from 9.1 then bounds all fixed motifs.
The c choice precedes every fixed interval and width constant.

## Every motif and list is counted

The bounded integer offset pool has exactly 2W+1 elements. A proved finite
subset-weight bound controls all its subsets of size <=floor(c*loglogN)
by exp(1)*(2W+2)^floor(c*loglogN). The actual logarithmic bound and the
proved loglog-squared/logN limit make this uniformly subpolynomial for
every fixed polylogarithmic width. The finite product of motif codes is
counted before the varying old set or centre list.

The list predicate admits some actual nonempty even motif at each index
and requires their parity sum to belong to the full old space. A literal
finite cover by actual motif functions and actual projected-tuple fibres
counts all lists. The subtype-to-natural centre map is injective. Thus
no target list count, motif enumeration or local projection estimate is
assumed as a premise.

## Source scope and improvement P1-MATH-0060

The source block formulation uses B=L+1 in the critical band, with every
old block of cardinality <=Dold*B and every new offset of absolute value
<=W<=D*B. The union has O(logN) generators by the proved critical-band
scale. Every fixed comparable positive centre interval is included, and
one threshold precedes all old blocks, motifs and lists. Uniform positivity
and equality with the literal signed split product are proved at that same
threshold. Evenness and nonempty source selections are explicit.

The stronger core permits any old generator set of size <=E*logN, with
arbitrary geometry and value heights, and every fixed polylogarithmic new
width. Only the generator count enters the estimate. This is the recorded
improvement P1-MATH-0060. The later conditional full-support theorem 10.1
is not asserted here.

No new unproved literature input, Paper C port, original manuscript-byte
change or Palomar registration is introduced.

Verification checkpoint: Lean v4.36.0-rc2 full build passed (9,707 jobs); actual axiom audit passed for all 4,270 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 1,985 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 17.39 GiB. No unproved projection/list count, new literature input, new Paper C port, manuscript-byte change or Palomar registration.
