# Complete actual short split-product moments — article 9.1

Proposition 9.1 and its Lᵛ consequence are proved under the actual infinite
prime-sign measure. Coverage is 58/167 (main 18/73, companion 40/94).
The main declarations are `ShortSplitMoments.article_9_1` and
`ShortSplitLpBounds.small_c_lpNorm`. The original manuscript is preserved.

## Exact moment and actual prime patterns

For every finite positive natural-valued family X and every even v,
`MultiplicativeMoments.infinite_even_moment` proves that the actual Bochner
integral of |sum_i f(X_i)|^v equals the cardinality of all tuples with
square product. Repetitions are included. A finite prime cutoff is
constructed inside the proof and actual cylinder expectation transport
and character orthogonality evaluate the full sum. No integrability,
independence or square-tuple count is assumed as an external premise.

The canonical kernels retain the square-product condition exactly.
For squarefree q_i with square total product, each prime is assigned to
its actual occurrence subset. These subsets have even size >=2. The
constructed d_S are positive, squarefree, pairwise coprime, reconstruct
each q_i and are unique among such representations on the even patterns.

## Actual exposure and a simpler finite exponent argument

For an actual injective rank, e_i is the product of the d_S with i in S
and some earlier index in S. It divides q_i, and q_i=e_i*newPart_i.
At the last index every relevant pattern has already appeared, so e_last
is the entire q_last. The logarithmic divisor is proved to equal the
prescribed weight in the finite exposure calculation.

The correction summed over exposed indices depends only on the last one:

    correction(last) = sum_S (1-|S|/2)*alpha_S + beta_last/2.

For nonnegative alpha_S and |S|>=2, choose a last index with minimum beta.
Then correction <=sum_S |S|*alpha_S/(2v). A genuine injective rank with
this last index is constructed. This finite argument also permits odd
pattern sizes; evenness is needed separately for the actual square tuples.
This simplification and broader finite scope are P1-MATH-0058.

Actual heights q_i<=(KN)^d yield a total exposure exponent at most

    v/2 + log(K)/(2logN).

For actual split products, every fixed comparable positive source interval
is included. A common threshold before widths, offsets and centres proves
positivity, and the factor-height bound is derived with K=C+1. This finite
exponent estimate itself does not need d<=c*loglogN or even degree.

## New assignments are counted, not postulated

A squarefree pairwise coprime factor family of a fixed m has an injective
code assigning each actual prime of m to one factor. Its cardinality is
at most k^omega(m). At an exposure step, fresh patterns inject, by deleting
the current index, into the subsets of the other v-1 indices. There are
at most 2^(v-1) colours. The actual quotient m=q_i/e_i and its support
inclusion give the uniform cost

    N^(c*(v-1)*log2+epsilon)

at the derived q_i height and d<=c*loglogN. All finite factor counts and
prime support budgets are proved; no assignment count is assumed.

## Complete profile and prefix-state enumeration

At d<=c*loglogN, the actual pattern factors have a constructed dyadic
profile in a fixed finite product of integer ranges. Its cardinality is
uniformly <=N^eta for every fixed eta>0, before all varying data. A single
profile fixes the logarithmic lower weights and an actual exposure order.
The multiplicative coordinate upper bound is 2^H*N^beta_i, with H the
fixed number of even patterns. T5.2 absorbs this fixed factor uniformly;
no constant raised to an unbounded varying beta is hidden in the proof.

An actual prefix state stores earlier centres and every pattern factor
already seen. The state fixes e_i before applying T5.2 to the possible
current centres. At a fixed centre and e_i, the fresh factor family has
product q_i/e_i and is counted by its injective prime code. The resulting
actual record count determines the next state. At the last index its
kernel is fixed, its fresh pattern set is empty, and the fixed-kernel
T5.2 estimate counts the possible centres directly.

The finite image/refinement inequalities are proved and applied to these
actual records. Iteration bounds the complete tuple set. The source
coefficient c*[v*(v-1)+2]*log2 and all arbitrarily small exponent losses
are retained. The finite profile cover then gives the full tuple count,
and exact moment expansion proves

    E |sum_{n in S} f(P_A(n))|^v
      <= N^(v/2+c*[v*(v-1)+2]*log2+epsilon).

No tuple, prefix, assignment or centre count is an unproved premise.

## Exact source range and Lp consequence

The result holds for every fixed real a>0,b and every finite subset
S of [a*N,b*N], including the source intervals of comparable height and
length. It holds for every fixed width D*(logN)^A0. Uniform positivity
and the literal signed-product identity are proved at the same threshold
as the moment bound. This broader scope is P1-MATH-0059.

The actual sum is AEStronglyMeasurable and MemLp for every exponent. Its
real lpNorm is identified with the actual integral's v-th root. For each
fixed even v>=2 and epsilon>0, the proof chooses

    c = epsilon*v / (2*[v*(v-1)+2]*log2) > 0.

This c is chosen before every fixed interval and width constant. Both the
real lpNorm and extended eLpNorm are bounded by N^(1/2+epsilon) after a
common threshold before all motifs and centre subsets. The source even
order and even degree are retained. Corollary 9.2 is not included in this
completion.

The earlier finite-foundation checkpoint and its verification remain in
Git history. No new literature input, Paper C port, original manuscript
change or Palomar registration is introduced.

Verification checkpoint: Lean v4.36.0-rc2 full build passed (9,683 jobs); actual axiom audit passed for all 4,226 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 1,941 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records remain intact. Ubuntu available space: 17.43 GiB. No unproved arithmetic/tuple count, new literature input, new Paper C port, manuscript-byte change or Palomar registration.
