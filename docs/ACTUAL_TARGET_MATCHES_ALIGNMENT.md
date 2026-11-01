# Actual compatible target matches — partial T2.6 and T1.11

Primary source: companion T2.6, page 22, `p1:arith:fixed-channel-rank`,
`companion_sections/supplemental_arithmetic.tex:209`, statement hash
`8dd614c19e50df20ed1eb9f3ab37c07386f1ce3665c3499e26d83211ceab60b9`.
The same bridge is used by T1.11, page 15, `p1:arith:palmrank`,
`companion_sections/arithmetic_appendix.tex:861`, statement hash
`f5c10336a982eb463bd69da026b36971a8d8bbede48fd0ad27463a97cfe6a307`.
Both numbered rank statements remain **in progress**.

## Exact counted object

Write B=L+1 and V_x={x-1,...,x+L-1}. The old normalized set is
U=b*V_x union a*V_y, with each value counted once.
`ActualNormalizedMatches.exactOffsets` consists exactly of the actual
indices k in Fin B for which a*b*d*(z+k-1)=c*n for some n in U.
It does not replace U by its enclosing interval.

If source labels at i0,j0 equal a*t,b*t and d*z=c*t+h, every such
index lies in one of the two affine divisibility classes previously
counted. The integer offset map is injective. Thus the finite class
bound gives the actual bound for nonphysical fractions. This uses
only an inclusion, without an unjustified converse.

`CompatibleTargetMatches.goodEdge_parameter` obtains the positive
integer t and actual source indices from the paper's actual good-edge
definition, via dependence and private normalized coordinates.

## The two physical fractions

The divisor classification shows that the remaining reduced interior
fractions have d=1 and c=a or c=b. Positive actual pair joint mass
implies that distinct start centres are at least L apart. Therefore
their complete windows have at most one common value, including the
possible common boundary value. Equal positive dilations preserve this
intersection cardinality. The other normalized family contributes at
most B/b+1, giving **B/b+2** in either physical case.

`PhysicalNormalizedMatches.physical_card` identifies the match count
with the actual normalized set intersection. The proof does not infer
window separation from an abstract independence premise: it takes a
common realization from the positive actual joint event and applies
the deterministic start separation theorem.

## Combined finite bound and remaining rank argument

For a>0, b>=3, a<b, coprime a,b, positive coprime c,d and
b/2<c/d<2a, `CompatibleTargetMatches.compatible_match_bound` proves

    card(actual matching positions) <= B*gamma_{a:b}+3.

It assumes positive pair joint masses for the two distinct target/source
pairs, positive centres and L>0, and the actual source/target affine
identities above. `compatible_triple_match_bound` derives both pair
premises from positive actual triple mass. There is no height cutoff.
The physical estimate is absorbed using gamma>=1/b. These explicit
finite constants and the actual-set bridge are P1-MATH-0038.

The residual normalized rank, endpoint-source count, endpoint separation
and extension by old prime information are still open. In particular,
this position count is not asserted to equal an actual rank loss. No
extra numbered result is counted complete. No external mathematical
premise or Paper C port is added; original manuscript bytes remain
unchanged and no Palomar registration is made.

Validated actual matching checkpoint for T2.6/T1.11 and P1-MATH-0038:
[4212bf9ec45186af0f1ce85ed9a6fea00542775e](https://github.com/Vulkin-prog/paper-p1-lean/commit/4212bf9ec45186af0f1ce85ed9a6fea00542775e).


Later extension: deterministic separation now suffices for this actual
matching bound. Explicit dyadic endpoint-source families and target pools,
with one common critical-band threshold for bounded affine data, are proved
in the [dyadic checkpoint](DYADIC_MATCHING_ALIGNMENT.md). The finite
[target quotient-rank bridge](TARGET_QUOTIENT_RANK_ALIGNMENT.md) is now
proved, including old prime information; its full asymptotic application
remains open.
