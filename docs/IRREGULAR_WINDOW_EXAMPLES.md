# Two concrete irregular-window examples

The nine theorems in
[IrregularWindowExamples](../PaperP1/Model/IrregularWindowExamples.lean)
give finite examples for the two notation distinctions in the
[editorial handoff](EDITORIAL_HANDOFF_AFTER_ENDPOINT_REVIEW.md).
They concern the actual run-start model: the preceding value has the
opposite sign, and all L values inside the window have the same sign.

## Formal and effective kernels

Take x=18 and L=10, with prime cutoff M=28. There are nine prime
coordinates: 2,3,5,7,11,13,17,19,23. The ten run rows have rank nine.
Their homogeneous kernel on prime samples is zero; the compatible affine
fiber contains the single sample with prime17 negative and all other
prime coordinates positive. Thus the actual infinite-model marginal is

    p_18 = 2^(-9) = 1/512.

The full formal row-relation kernel has dimension one. Its local
relation can be seen in the even square product
18*24*25*27=540^2; none of those vertices is the left boundary.
The nominal formula therefore gives the correct value

    2^(-10) * 2^1 = 1/512.

By contrast, a singleton family always has effective relative nullity
zero: passing to each window's effective image already quotients out
its internal row relations. Substituting this relative nullity into
the formula while retaining the nominal marginal would give 1/1024.
The theorem `IrregularWindowExamples.effective_kernel_nominal_fails`
formally proves that this substitution is false.

The correct effective-kernel formula retains the actual marginal 1/512.
This example explains the raw/effective distinction in T22.7. It does
not refute the printed nominal formula with its formal-kernel meaning.

## Homogeneous probability and original affine probability

Take x=3 and L=7. A run would make the values at 3,...,9 all equal.
The square4 forces their common bit to zero. The product6=2*3 then
forces the bit at2 to zero as well. This contradicts the run's left
boundary equation, which requires the bits at2 and3 to differ.
Consequently the actual original marginal is zero.

The homogeneous event, in contrast, asks that the preceding and all
inside values agree. It is compatible with all prime bits zero and
has positive probability. The theorem
`IrregularWindowExamples.homogeneous_positive_original_zero` proves
both facts for the actual infinite measure. This illustrates why the
homogeneous mass clause of T8.2 cannot be replaced by the original
affine marginal weight at irregular windows.

These examples are algebraic illustrations at specified small parameters.
They do not assert that those parameters exceed any asymptotic threshold,
introduce a third false-original statement, or add a registry selection.
All frozen TeX and PDF versions are preserved.

The complete [checkpoint1003 replay](validation/checkpoint-1003/validation.json)
at source `3df7615af2aa6a2a2bc6856bd4203c401d0434de` passed 18,627 build
jobs, 19,984 theorem axiom checks and 19,907 distinct references, with all
three actual process exits zero. The permitted kernel axioms remain
propext, Classical.choice and Quot.sound. The exact compiled types and
individual axiom reports of all nine example theorems accompany that
record. A [separate review instance](reviews/2026-11-07/irregular-examples.json)
also read every example type, proof body and relevant event definition;
it found no additional mathematical gap and did not execute the parent's
builds. Palomar submissions remain on hold at the user's request.
