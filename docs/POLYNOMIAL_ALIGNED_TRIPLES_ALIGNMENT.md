# All interior distinct-slope aligned targets at polynomial height

The interior distinct-physical-slope aligned-target sector of
main 14.3 is now unconditional at arbitrary fixed polynomial target
height, with arbitrary affine offsets and without local regularity,
private normalized primes, even-map injectivity or an assumed
compatibility witness.

Fix a reduced source channel 0<a<b<2a and a natural J before N.
Actual source vertices satisfy label_x(i)=a*t and label_y(j)=b*t.
A reduced target c/d satisfies d*z=c*t+h, with d<=B^J and
|h|<=B^J. The three physical slopes a*d,b*d,c are required distinct
and in the strict interior ratio range: c<2*a*d and b*d<2*c.
Every actual dyadic triple with these data is covered, including
arithmetically exceptional source pairs and irregular local windows.
Zero-probability incompatible systems are included in the upper bound.

The existing checked TargetUnionResidual estimate already bounds the
actual omitted-prime row space by an arbitrarily small multiple of B,
uniformly in c,d,h. The full merged-value kernel embeds in this row
space. A new finite algebraic estimate bounds the full span of any
three finite sets by the sum of their local even spaces plus three
anchor directions; it needs no intersections or connected-overlap
assumption. Hence union.card <= actual joint rank + full kernel rank+3.

The physical triple is automatically primitive because the source
and target ratios are reduced. Its three possible orderings transfer
the canonical finite bound of P1-MATH-0099 to the actual old/new merged
set by a common integer dilation. This gives actual joint rank at
least (71/30)*L-5-o(L), and actual infinite-model joint probability
at most N^(-71/30+epsilon). No total-rank bound, compatibility or
point probability is supplied as a premise.

A literal source/target parameter pool enumerates t<3N, the B^2 old
vertex choices and every member of the actual affine target pool.
It has cardinality at most 18*a*N*B^(3J+2). A checked source
membership theorem reconstructs the original x,y,z from these codes;
the numerator bound c<=2*a*B^J follows from dyadic geometry. The final
finite host set retains exactly three-element families with actual
representations and the stated physical conditions. Every qualifying
actual source is included after one common critical threshold.
Its cardinality is at most N^(1+epsilon) and its actual joint mass
is at most N^(-41/30+epsilon).

A separate checked geometric helper shows that three normalized
windows with connected overlap lie in one interval of radius 5*Q*B
around the first normalized center when their multipliers are <=Q.
It supplies exact interval and macroscopic base bounds and a
common-point connectivity construction; the growing-height probability
and mass proof does not assume this connected-overlap criterion.

This extends findings P1-MATH-0067 and P1-MATH-0099 and the partial
main 14.3 correspondence. Nonaligned targets, repeated physical
slopes and dyadic endpoint populations remain open in the full source
proposition. The lower bound for the total third factorial cumulant
also remains open. Coverage stays 79/167 and confirmed improvements
stay 99. The source manuscripts, dependencies, external-input scope
and Palomar state are unchanged.

Verified with Lean v4.36.0-rc2: full lake build (11199 jobs), actual kernel-axiom audit (7463 declarations; only propext, Classical.choice and Quot.sound), 5180 ledger/finding declaration checks, all 138 source manifest entries and 167 numbered-result hashes preserved; 14.73 GiB free on Ubuntu root.
