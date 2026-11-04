# Clean directed arithmetic pairs and actual target cost

Sources: companion T19.16 and T19.17, limits_appendix.tex:1214 and1313, including the clean-pair constructions in their proofs. All original source hashes are preserved in the numbered ledger.

Companion T19.16 and T19.17 gain a finite clean arithmetic pair
ledger and exact positive target costs in the ORIGINAL prime cylinder.
Both numbered results remain IN PROGRESS: no asymptotic forcing lower
bound, logarithmic equivalent or ordinary smooth-value theorem is assumed
or claimed. Coverage stays 88/167 unconditional and 69 conditional, with
10 numbered results incomplete.

CleanPivotMultiples proves both sides of the actual multiple count in
every translated positive interval (A,A+N], with literal natural floors:

  floor(N/q) <= number of q-multiples <= floor(N/q)+1,
  N/q-1 <= number of q-multiples <= N/q+1.

For coprime q,r, the count satisfying q|n and r|n+k is at most
floor(N/(q*r))+1, uniformly in the interval position and offset k.
The proof uses differences from the least actual solution. It does not
postulate the existence or density of a CRT residue class.

CleanPivotTargets retains q|n, excludes q^2|n and excludes every other
selected prime r from every target position 0..B-1. The membership test
and the finite union/deletion ledger are exact. If q>=Y>0 and every r>=Y,
with each r coprime to q, its actual clean target count is at least

  N/q - 1 - (|R|*B+1)*(N/(q*Y)+1).

This separates the valuation loss from every other-pivot collision and
keeps all endpoint +1 terms. No scale restriction on Y or B is used.

CleanPivotPairs retains each distinguished source j and sums its actual
target fibre injectively. Put S_q=sum_{j in J}1/q_j and suppose each
source has at most S other selected primes. The total clean directed
pair count is at least

  N*S_q - |J| - (S*B+1)*((N/Y)*S_q+|J|).

After deleting arbitrary exceptional target set T and arbitrary exceptional
PAIR set D, the same lower bound loses only |J|*|T|+|D|. In particular a
global exceptional pair set is charged ONCE, rather than once per source.
Neither set's cardinality is assumed small. All finite counts precede
the reciprocal-pivot, smooth-value and raw-dependence asymptotics.

PrivatePivotTargetFlip connects those literal divisibility predicates
to the actual arithmetic field. The original forceWord changes a raw
value by the sum of its true selected-prime parity contributions. If q is prime,
q divides n and q^2 does not divide n, its valuation at n is exactly
ONE and hence its parity is one. Privacy above the
target width excludes that prime from the other target positions. Every
other changed prime is excluded by the actual clean-target predicate.
Thus the entire original target vector changes by exactly

  targetWord_after = targetWord_before + single_0(source_correction).

For the anchored map the correction is the exact original source bit
minus its template bit and anchor-determined orientation. No arbitrary
target flip is substituted for this physical prime modification. The
other-prime population has at most card(source)-1 elements. Its coprimeness
and cutoff conditions follow from actual distinct prime coordinates.

UniformLinearObservation proves that a surjective finite binary linear
map has the full uniform output law for every real observable, using the
existing actual affine fibre probabilities. RawWordObservation applies
this to the JOINT original source and target raw-value matrix. Its
surjectivity gives the actual independent uniform two-word law.
Clean divisibility alone does NOT imply this surjectivity. That finite
matrix condition remains explicit in each pointwise expected-cost theorem.

CleanPivotWordCost combines the actual target transformation with that
proved observation law. For a clean target with a surjective joint matrix,
the expected absolute change of a prescribed signed target word of length
B is EXACTLY 2^(-B). For a deterministic anchored source and an unsigned
two-orientation target of length B>=2, it is EXACTLY 2^(-(B-1)). These
are expectations in the original finite prime cylinder. Source/target
independence is discharged from matrix surjectivity; no conditional Palm
law or cost value is a theorem premise. The finite correction rates match
the signed and anchored uniform-word calculations already proved.

PositiveForcingCostLower identifies the full directed offsite sum with
the original nonnegative coordinate-cost ledger. Every selected clean
directed pair can be retained for a lower bound. The diagonal remains
separate and nonnegative, so the same selected-pair lower bound applies
to the full source-deleted cost. There is no cancellation, unordered-pair
quotient or implicit symmetry factor.

The final dyadic population restoration, quantitative bounds for the
exceptional target and raw-dependence pair sets, the ordinary smooth-value
short-interval input, sharp reciprocal-pivot saddle comparison and final
asymptotic summations remain unformalized. The finite arithmetic counts
and actual pointwise expected costs are not counted as a completed
T19.16 or T19.17. The existing half-count theorem uses EVEN effective
selections and is not silently applied to full raw-value relations.

P1-MATH-0181 records the explicit clean arithmetic deletion constants,
the once-only global pair-exception charge, and the actual prime-cylinder
single-bit cost bridge. There are 180 confirmed improvements and one
statement-scope correction. All new arguments use existing P1/Mathlib
foundations, with no new PaperC port, external mathematical premise,
dependency download, compiler change, axiom or source-manuscript edit.
Palomar remains deferred until full coverage and statement alignment.
