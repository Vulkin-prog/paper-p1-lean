# The one-small-kernel assertion of companion T1.13

The first assertion of companion T1.13 is proved for arbitrary actual
selected subsets in fixed-width translated intervals. T1.13 remains
**in progress**: its two-small-kernel assertion requires the separate
T1.5 estimate and is not proved here.

Source: `companion_sections/arithmetic_appendix.tex:1016`, page 17,
`p1:arith:small-kernels`, statement hash
`abfe0badc4580784052dd0b667c0f6e3fcb66cb7df81671a5a21b1c20132fb97`.

## Arbitrary actual selected blocks

`SmallKernelBlocks.selectedStarts G V H T` is the actual set of integer
centres x in G with some n in the selected positive-integer set V(x)
whose actual H-kernel is at most T. The subsets V(x) may depend on x.
For every finite integer offset set O containing all differences n-x,
this family is proved to lie in `starts G O H T`.

At a fixed offset u, the map x -> (x+u).toNat is injective on the
positive translated values. If every candidate value is at most X,
its image lies in the actual bounded-kernel value set of
`RankinSmallKernel`. Summing over offsets gives

    #starts <= #O * #bounded-kernel values,
    #starts <= 2*#O*sqrt(X)*sqrt(T)*exp(2*sqrt(H)).

No regularity, independence, positive event probability, lower centre
bound or comparison between H and the block diameter is needed for
this one-kernel estimate. Positivity of selected values is explicit.
The real cutoff T may be any nonnegative number.

## Uniform logarithmic and critical-width forms

`SmallKernelBlockCount.arbitrary_selected_blocks` proves, for fixed
nonnegative K,D,E and every epsilon>0, one threshold preceding all
centres, offset sets, selected subsets, heights, cutoffs H and real T>=0.
Under #O<=D*log(N), H<=E*log(N), X<=K*N and the candidate height bound,

    #selectedStarts <= N^(1/2+epsilon)*sqrt(T).

`FixedWidthSmallKernel.one_kernel_real` supplies the literal fixed-width
form. For fixed real upper centre coefficient K, width D>=0 and cutoff
coefficient E>=0, every critical-band length L and cutoff H<=E*(L+1)
use the same threshold. The sets V(x) consist of positive integers
satisfying |n-x|<=D*(L+1), and the centres satisfy x<=K*N. Their actual
one-small-kernel starts satisfy the displayed bound for every real T>=0.

The integer interval cover has exactly 2*R+1 offsets. Fixed real K,D
are enlarged to their natural ceilings, with both actual height and
offset membership inequalities proved. The selected family is only
enlarged by the cover. There is no need to replace it by an equality
with the enclosing interval. This includes the paper's range 1<=T<=C*N
and arbitrary selected subsets U_X of a fixed-width logarithmic interval.

## Remaining scope

These new P1 modules use the already proved square-root endpoint of the
small-kernel Rankin estimate and logarithmic subpolynomial factors.
No new Paper C code or unproved literature input is introduced.
The broader one-kernel scope extends P1-MATH-0046. T1.6 remains complete,
while full T1.13 and T1.14 remain open in their two-small-kernel regimes.
Numbered coverage remains 54/167.

`realSelectedStarts_eq` proves exact equality of the actual real-prime-
cutoff family with its natural-floor family.
`one_kernel_real_cutoff` therefore retains arbitrary real prime thresholds
Y>=0, Y<=E*(L+1), under the same threshold and all real T>=0.

The full build passed (9,447 jobs); all 3,667 declarations passed the
actual axiom audit, permitting only propext, Classical.choice and
Quot.sound. All 1,382 distinct coverage/finding names were checked
directly by Lean. Original manuscript bytes are unchanged.

Validated selected fixed-width one-kernel checkpoint (9,447 build jobs;
3,667 audited declarations; 1,382 directly checked coverage/finding names):
[77be471d8c127edb6104caae2922aaef3a95ec54](https://github.com/Vulkin-prog/paper-p1-lean/commit/77be471d8c127edb6104caae2922aaef3a95ec54).

Subsequent scope update: T1.14 is now complete by the independent stronger
conditional half-count proof, including its actual fixed-width parameter
records. The separate two-small-kernel assertion of T1.13 remains open.
See [the complete T1.14 alignment](SEVERAL_BLOCK_RELATION_ALIGNMENT.md).
