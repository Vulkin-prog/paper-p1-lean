# Unrestricted raw-dependence hosts in logarithmic windows

Sources: companion T19.16 and T19.17, limits_appendix.tex:1214 and1313, including the clean-pair constructions in their proofs. All original source hashes are preserved in the numbered ledger.

Companion T19.16 and T19.17 now have the unconditional uniform full
RAW two-window dependence exception bound. For every fixed D>=0 and
epsilon>0 there is a threshold N0, independent of the moving width,
word lengths and prime-cylinder cutoff, such that for N>=N0,
1<=B<=D*log N, S,T<=B and M>=2N+B,

  # {(x,y) in [N,2N)^2 : the joint S/T raw-word matrix is not surjective}
       <= N^(3/2+epsilon).

The words are the actual original values x-1+i and y-1+j. No evenness
condition is imposed on either block. Local relations, repeated windows,
and diagonal host pairs are included. This fills the full raw host
exception estimate used in the lower-bound arguments; it does not prove
the final forcing asymptotics or mark either numbered result complete.

RawTwoWindowHosts defines the full nonzero two-block parity relation.
At least one selected coordinate anchors the relation, in one of the two
orientations. Every actual largeOddKernel is at least one, so the cutoff
T=1/2 retains every such anchor. Applying the existing unconditional
LargeAnchorPairs finite bound with tau=1/2 yields

  #hosts <= 8*B*N*sqrt(3N)*exp(K*sqrt B),
  K=2+PowerSeriesTail.constant(3/2).

In particular the argument requires neither prime number theory nor a
new PaperC port. It does not use the effective EVEN-space half-count.
UniformSubpolynomialPower converts the exact reciprocal-power convention
into a literal N^epsilon bound. RawTwoWindowHostCount proves that
8*sqrt(3)*(B+1)*exp(K*sqrt B) is uniformly subpolynomial throughout the
entire upper logarithmic band. The width need not have a fixed offset
from a critical length. The threshold is selected before the width.

RawValueIndependence proves the needed original matrix bridge. Injective
row relations give strictly positive mass to every output, hence
surjectivity. A non-surjective actual value system therefore supplies a
nonzero row relation. Evaluating it on every actual prime basis vector
recovers the full integer factorization-parity relation: primes above
the cutoff do not divide any positive observed integer, and nonprime
coordinates vanish. The two-block coefficient word splits into the two
unrestricted source and target selections. Thus non-surjectivity of the
joint raw matrix really is contained in the full arithmetic host set.
There is no independent-word premise in this exception count.

RawDependencePairs also proves that surjectivity for two maximal words
implies surjectivity for their shorter, possibly different, initial
segments, by extending both prescribed output words to the maximal
length. Rectangular non-surjectivity exceptions are therefore contained
in the same maximal bad-pair set. RawDependenceCount gives both literal
uniform bounds, with the cylinder cutoff quantified last and uniformly.

P1-MATH-0182 records this parity-complete raw exception estimate and its
actual finite-cylinder interpretation. The finite clean arithmetic
ledger can now discard raw-dependent pairs using a proved bound.
Endpoint translations, excluded-source/target counts, reciprocal-pivot
saddle comparison, full-value weighted upper profiles, ordinary smooth
integers in almost every short interval and final asymptotic cost
summations still require their own arguments. Neither T19.16 nor T19.17
is declared complete. Coverage remains 88 unconditional and 69
conditional results out of 167, with ten numbered results incomplete.
No source-manuscript byte, dependency or compiler version is changed.
Palomar remains deferred until completion and statement alignment.
