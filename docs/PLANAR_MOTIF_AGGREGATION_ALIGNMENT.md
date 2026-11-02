# Complete companion T20.6: planar transverse products

Companion T20.6 is now complete, including the exact finite host
population and original affine primitive mass. All thresholds are chosen
before the length, integer prime cutoff, plane family, centers and motif
population. The final source population has the real cutoff H=C0*B,
real coefficient exponent K, at most B^K planes, nonzero integer normals
and all normal and constant coefficients bounded by B^K. Regularity,
distinct centers and pairwise direct effective square-class spaces are
retained exactly.

The finite budget of 3B formal window positions selects three disjoint
transverse motifs with a fixed size bound depending only on eta. It
never enumerates the macroscopic family or any covers. The actual
positive motif products have canonical odd-prime support codes, and
multiplying by the product of those codes gives an actual integer
square. Small-prime coefficient codes and bounded offset motifs have
N^epsilon choices, uniformly over every H<=C0*B. There is no bound on
the height of the resulting square coefficients in the arithmetic step.

A plane meeting the dyadic region with |h|<N has a positive and a negative
normal coefficient. A checked permutation orients that pair; relabeling
preserves all actual motif products, small-prime codes, sizes, disjointness
and transverse supports. Six permutations suffice. The oriented fixed-plane
count is summed over all motifs, codes and planes. This gives at most
N^(1+epsilon) ordered hosts, with no external Pila or BCN premise.
The exact real-to-integer cutoff equivalence uses the natural floor.

The actual affine joint probability of any such triple is at most p^2
by restricting to its direct regular pair. Summing the exact probabilities
gives mass at most N^(-1+epsilon), even before restricting to primitive
triples. The primitive mass is defined as the literal filtered sum and
inherits the same bound, including all incompatible zero-probability cases.
The weaker hypotheses and the three-equation argument complete confirmed
improvement P1-MATH-0097. No new improvement identifier is counted for
this completion of the same proof.

T20.6 moves from in progress to proved. Numbered coverage becomes 79/167
(main 28/73, companion 51/94); confirmed improvements remain 97.
This does not establish the six-vertex exclusion T20.8, the general
unrestricted two-parameter count T1.7, or the dense weighted pair sector.
No original manuscript, dependency version or Palomar registration is
changed.

Verified with Lean v4.36.0-rc2: full lake build (11091 jobs), actual axiom audit of all 7173 theorem/lemma declarations, direct Lean checks of all 4890 ledger/finding references, source integrity (138 manifest entries and 167 numbered statements), and git diff --check. Only propext, Classical.choice and Quot.sound occur; no sorry, admit, native_decide, or new axiom was added. Ubuntu root space after verification: 14.94 GiB.
