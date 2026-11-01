# Actual short-product moments: finite foundations

Article Proposition 9.1 remains in progress. This checkpoint proves its
actual probability identity and finite arithmetic/exposure inputs; it does
not claim the final asymptotic tuple count. Coverage remains 57/167.

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

## Remaining work before Proposition 9.1 can be marked proved

The size profiles must be enumerated uniformly and the exposure estimates
assembled over actual prefix states, with their prescribed divisors fixed
before applying T5.2. The last fixed-kernel fibre and all accumulated
errors must then be summed. These steps remain open. An exponent identity,
a prime decomposition or an abstract implication assuming the target count
is not recorded as a completed moment bound.

No original manuscript bytes are changed and no Palomar registration is
made at this preparatory checkpoint.

Verification checkpoint: Lean v4.36.0-rc2 full build passed (9,653 jobs); actual axiom audit passed for all 4,162 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 1,877 distinct ledger/finding declarations were directly checked. All 138 manifest entries and 167 numbered records remain intact. Ubuntu available space: 17.49 GiB. No unproved literature input, new Paper C port, original manuscript change or Palomar registration.
