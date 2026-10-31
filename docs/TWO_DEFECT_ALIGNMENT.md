# Two-defect window counts: exact statement alignment

This completes the two-defect-window conclusion inside companion T1.3
(V1.6 page 6, `p1:arith:defects`, source line 90), equation
`p1:arith:twodefect`. T1.3 as a whole is now complete; see
[the complete alignment](DEFECT_COUNTS_ALIGNMENT.md).

## Actual sets and uniformity

`TwoDefectHosts.twoDefectStarts H R X` contains precisely the positive
integer starts x ≤ X with two distinct offsets i,j in [0,R] such that x+i
and x+j have K_H=1.

`TwoDefectCount.two_defect_count_le_rpow_eventually` proves that for
fixed real C,D,E ≥ 0 and ε > 0, one threshold works for every N and every
H,R,X satisfying

`H ≤ D log N, R ≤ E log N, X ≤ CN`.

The cardinality of that actual set is ≤ N^ε. The threshold precedes every
cutoff, width and counting height.

`TwoDefectWindows.dyadicTwoDefectWindows N H L` uses exactly [N,2N) and
the vertex interval [x-1,x+L-1] from the paper. Membership, the injective
shift x ↦ x-1 for N ≥ 2, and the comparison with the preceding set are
proved. Consequently,

`dyadic_two_defect_windows_le_rpow_eventually`

proves the literal dyadic-window count ≤ N^ε uniformly whenever
H ≤ D log N and L ≤ E log N. This retains the left boundary vertex.
The final statement assumes neither a nonsquare coefficient ratio nor an
unproved equation-count bound.

## Finite arithmetic and counting proof

Every actual defective value has its canonical small-prime-support times
square representation. For two distinct offsets, the equation is exactly

`c₁ a² - c₂ b² = i-j ≠ 0`.

The offsets and support sets form an explicit finite configuration set.
Its size is at most `(R+1)² · (2^π(H))²`. Every actual start belongs to the
image of an actual positive quadratic solution associated with one
configuration; a solution determines the start by `x=c₁a²-i`.

The support products are positive and at most the primorial, hence at most
4^H. For logarithmic H they have polynomial height with one fixed exponent
K ≥ max(2,D log 4). The solution height X+R is also ≤ N^K after a threshold
depending only on C,E. The proved T1.2 estimate therefore supplies the
quadratic-solution count for every configuration.

The new prime-support proof derives

`π(H) ≤ 14 log(2)(D+2) log N / log log N`

uniformly for all H ≤ D log N once log N ≥ 4. It uses the elementary
Chebyshev estimate and a common rounded upper cutoff, so no lower bound on
H is needed. It follows that the actual number of prime subsets is
uniformly subpolynomial.

Apply the offset, support and quadratic bounds with error exponent ε/5.
The two squared factors and the quadratic factor multiply to N^ε.
All bounds are proved and supplied inside the final theorem. The generic
finite aggregation lemma's quadratic-count argument is thus discharged,
not retained as a literature or target-bound premise.

## Improvement and remaining work

The global count and this two-defect conclusion require only upper
logarithmic bounds on the cutoff and window width. This strengthening of
the original combined hypotheses is recorded as P1-MATH-0003. It does not
change any exponent or claim the local O(B/log B) conclusion under unproved
parameter comparisons.

The local asymptotic prime budget and full fixed dilation/translation
statements are now also proved, completing T1.3. Numbered-result coverage is 9/167.
The new P1 proofs use already recorded and audited inputs; no additional
Paper C source file is copied for this step. Full compilation and the
actual axiom audit pass for all 862 current proved declarations.

