# Companion T22.2: when no relation meets every block

**Status: proved**, both the one-family inequality and its ordered-tuple
summation. Coverage is 15 / 167: 8 / 73 main and 7 / 94 companion.
Original locator: companion V1.6, page 90, `p1:uniform:missing-block`,
`companion_sections/uniform_appendix.tex:69`. The original statement hash
and manuscript bytes are unchanged.

## The structural premise and exact kernel cover

The effective spaces are the actual `squareClassSpace x L`. The premise is
the literal absence of a tuple of nonzero effective classes, one from each
block, whose sum is zero. It is not replaced by a claim of independence or
by a bound on the target probability.

`Affine.subfamilyKernelExtend_has_preimage` reconstructs any relation
vanishing outside a subfamily by extension by zero. If no relation has full
support, every relation vanishes in some block. Consequently
`erasedKernelToFull_surjective` maps the disjoint union of the one-block-
deleted kernels onto the full kernel. Cardinality gives

`2^rho(I) ≤ sum_{x in I} 2^rho(I.erase x)`.

Both the natural and real versions are proved. Kernels and nullities are
those of the actual effective spaces, so local relations are not counted twice.

## Actual probabilities and incompatibility

`MissingBlockProbabilities.infiniteJointMoment_antitone` proves monotonicity
under event inclusion. If the complete joint probability is positive, every
subfamily probability is positive and the already proved exact affine mass
formula applies to each erased family. Multiplication of the kernel-cardinal
bound by the complete product of exact marginals gives

`q(I) ≤ sum_{x in I} p_x q(I.erase x)`.

`infinite_joint_missing_block_bound` proves this under the actual infinite
prime-sign measure for any positive length L and any finite family. If the
full event is incompatible, its probability is zero and the right side is
nonnegative. No positive-marginal or compatibility filter is imposed.

For regular windows, every p_x is exactly p=2^(-L), as proved in main 3.1.
`regular_joint_missing_block_bound` therefore gives the source's
`q(I) ≤ p sum_x q(I.erase x)`.

## Ordered distinct tuples and exact factorial moments

`Probability.OrderedTuple G r` is the type `Fin r ↪ G`. Distinctness and
membership in G are part of the object. `tupleValues` is its actual set of
sites, and its cardinality is proved to be r.

`eraseTuple` deletes a chosen coordinate with `Fin.succAboveEmb`, retaining
the order of the other coordinates. `tupleValues_erase` proves that its site
set is precisely the erased original set. `eraseTuple_encoding_injective`
proves that the omitted value and the remaining tuple determine the original
tuple. Thus for each marked position, summing a nonnegative erased-tuple
weight over any tuple family is at most |G| times the sum over every remaining
ordered tuple. This is `sum_erased_tuple_bound`.

`FactorialTuples.activeTupleEquiv` identifies the active ordered tuples with
embeddings into the actual active-site set. Its cardinality is the falling
factorial of the actual count, by Mathlib's proved embedding-cardinality
formula. No independent Bernoulli model is introduced.

`FactorialCountMoments.factorialCountMoment G L r` is the actual Bochner
expectation of that falling factorial. Its equality with the usual real
product `prod_{i<r}(Z_G-i)` is proved, including counts below r, where both
products vanish. `sum_tuple_joint_moments` proves exactly

`sum_{t : Fin r ↪ G} q(tupleValues t) = E[(Z_G)_r]`.

The zero order, impossible tuple orders larger than |G| and all finite growing
orders are included. No uniform moment estimate or factorial tail is assumed.
`factorialCountMoment_two` gives `E(Z_G)_2=E Z_G^2-E Z_G`, retaining the diagonal.

## The complete summed conclusion

`MissingBlockTupleSum.companion_T22_2_sum` proves the source's estimate for
every deterministic subfamily of ordered distinct regular-window tuples.
The tuple order R is written r+1, and the remaining factorial order is
r=R-1. Summing over the R omitted positions yields

`sum_{t in A} q(tupleValues t) ≤ R N p E[(Z_G)_(R-1)]`.

The source context R≥2 is included; the finite proof also permits R=1.
There is no separation, primitivity, compatibility or cardinality cutoff
added to the premise. The missing-full-support condition is checked for
each tuple in the chosen family.

`sum_missing_block_tuples_card` retains the sharper |G| in place of N, also
allowing a deterministic subset of the complete regular set. More generally,
`sum_missing_block_tuples_heterogeneous` needs only a finite G⊆[N,2N), a
nonnegative common upper bound pmax for its actual marginals and the same
structural premise. It gives

`sum_{t in A} q(tupleValues t) ≤ R |G| pmax E[(Z_G)_(R-1)]`.

The ordinary marginal upper bound is the only extra parameter in this general
version. The original regular theorem discharges it by the exact proved
mass formula. Improvement `P1-MATH-0007` records the heterogeneous extension;
the original RNp statement remains a proved corollary.

## Validation

Lean v4.36.0-rc2 and its pinned matching Mathlib are used. The full build,
preserved-source checks and actual 1,334-declaration kernel audit were run
before the missing-block checkpoint was published. Only `propext`, `Classical.choice` and `Quot.sound` are
allowed. No Paper C source, external mathematical input or manuscript edit
is added. Palomar remains a later milestone.
