# Actual private rational triples: uniform mass and strict gap

The actual private zero-intercept rational sector of main 14.3 is
proved, uniformly at polynomial logarithmic slope height. For primitive
0<u<v<w<2u and t>=1, use product normalizers (v*w,u*w,u*v) on the
actual centers (u*t,v*t,w*t). A private normalized union implies actual
affine compatibility: its predecessors lie below their common origin
and every internal value lies at or above it. No affine positivity
surrogate is assumed.

Common integer dilation preserves exact intersection cardinalities.
Reducing each physical ratio gives pair intersection bounds
B*gcd(u,v)/v+1, B*gcd(u,w)/w+1 and B*gcd(v,w)/w+1.
The actual triple intersection contains all origin+u*v*w*m for
0<=m<=floor((L-1)/w); only this lower bound is needed. Exact three-set
inclusion-exclusion then proves that 3L-(union.card-1) is at most
D(u,v,w)*L+5. Thus the actual effective rank is at least
(71/30)*L-5, and it is at least (43/18)*L-5 away from the unique
extremal physical triple (10,12,15).

These are finite uniform bounds with no slope-height restriction.
They give original affine probability at most
2^(5+(71/30)*C)*N^(-71/30), or
2^(5+(43/18)*C)*N^(-43/18) in the nonextremal sector.
The existing sharp geometric gap P1-MATH-0067 therefore becomes an
actual probability gap on these private normalized triples.

For each fixed natural k, the exact population enumerates primitive
u,v,w<=B^k and t<2N, retains the actual dyadic and private conditions,
and maps the resulting parameters to actual center triples. A checked
source-membership theorem shows that every qualifying dyadic triple
with w<=B^k is included; the t bound is forced by its first center.
The parameter budget is at most 16*B^(3k)*N. Summing actual joint
probabilities gives mass at most N^(-41/30+epsilon), or
N^(-25/18+epsilon) away from (10,12,15), after one uniform critical
threshold. The same bounds hold for the literal unordered family
populations; positivity justifies any repeated parameter overcount.

Main 14.3 moves from not started to in progress. This checkpoint does
not cover arbitrary affine intercept motifs, nonaligned third targets,
nonprivate normalization, irregular starts, or endpoint/contact cases.
It is not the full source proposition, nor a total third-cumulant
bound. Main 14.5 retains its proved positive connected lower assertion
and its unresolved total-cumulant passage. Coverage stays 79/167 and
confirmed improvements stay 98. P1-MATH-0067 is extended by this
application; no new improvement identifier is counted. No external
Pila or BCN estimate, original manuscript edit, dependency change or
Palomar registration is introduced.

Verified with Lean v4.36.0-rc2: full lake build (11147 jobs), actual axiom audit of all 7329 theorem/lemma declarations, direct Lean checks of all 5046 ledger/finding references, source integrity (138 manifest entries and 167 numbered statements), and git diff --check. Only propext, Classical.choice and Quot.sound occur. Ubuntu root space after verification: 14.83 GiB.
