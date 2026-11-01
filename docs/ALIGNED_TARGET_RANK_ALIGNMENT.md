# Companion T1.11 and T2.6 — actual aligned-target rank

Both numbered statements are proved. Sources preserved from V1.6:

- T1.11, page 15, `p1:arith:palmrank`,
  `companion_sections/arithmetic_appendix.tex:861`, hash
  `f5c10336a982eb463bd69da026b36971a8d8bbede48fd0ad27463a97cfe6a307`.
- T2.6, page 22, `p1:arith:fixed-channel-rank`,
  `companion_sections/supplemental_arithmetic.tex:209`, hash
  `8dd614c19e50df20ed1eb9f3ab37c07386f1ce3665c3499e26d83211ceab60b9`.

## Literal source and target objects

B=L+1. One actual source unit gives positive integer t and actual
indices i,j with label_x(i)=a*t and label_y(j)=b*t. The reverse source
orientation is also covered. Thus the true compressed source is
U=b*V_x union a*V_y, centred about X=a*b*t, with radius at most bL.
The source theorem needs just this one unit, rather than private
coordinates, source regularity or affine compatibility.

The source families in T2.6 have at least two actual units, so they
satisfy this weaker premise directly. For a geometric good pair given
by private normalized coordinates and dependence, the proved
`geometric_good_source_units` supplies it without an affine event premise.
This includes the raw geometric family used by T1.11.

`CompressedTargetAlignment.Aligned D X z L` is the literal enlarged
geometric inequality

    |r*z-s*X| <= (r+s)*D*B,

for positive coprime r,s<=B^3. D is any fixed natural width multiplier.
For D=1, `of_geometric` embeds the original centre-alignment predicate.
Allowing arbitrary fixed D covers the fixed-width compressed interval.
`AlignedTargetRank.targets` is exactly the dyadic target set filtered
by this geometric predicate, rather than by an assumed affine encoding.

## Constructed reduced affine data

For B>=2D, `bounded_data` constructs positive coprime c,d and an
integer h with

    d*z=c*t+h,       d<=B^5,       |h|<=B^5.

Start with C=s*a*b and denominator r. The gcd divides the actual
integer displacement because X=a*b*t. Dividing numerator, denominator
and displacement therefore preserves the target equation. The reduced
displacement has absolute value no larger than the original one.
This is proved in `ReducedAffineData.reduce`; no rational-separation
or canonical-encoding input remains as a premise.

## True combined union and its residual

The actual finite sets are S=c*U, T=a*b*d*V_z and S union T, with
at most 3B distinct values. For bounded affine height H, actual dyadic
positions force c<=2aH. The true combined union has radius at most

    4*a*b*H*B

about c*b*label_x(i). It is covered by two literal progressions: a
c-dilate of the old enclosing interval of raw width 2bL, and the
(a*b*d)-dilate of the new actual window. The old enclosing interval is
used to bound residual rank; it is never used to count matches.

Discard exactly primes <=2bB and prime factors of c*(a*b*d).
The remaining prime rows meet at most two actual distinct values.
`TargetUnionResidual.row_rank_sublinear` applies the proved
Runge--Hamming--component argument with one uniform threshold before
all positions and polynomial-height target parameters. The whole actual
remaining-row kernel is o(L). Its coefficient prime budget, interval
location, logarithmic diameter and cardinality are discharged in Lean.

## Actual quotient deficiency and old prime bits

For any Q subset primeFactors(a*b), let W=S_x+S_y+primeSpan(Q).
`TargetWindowRank.deficiency` is exactly

    delta_Q = L-(rank(W+S_z)-rank(W)).

This includes every internal deficiency of the new window. The finite
true-set rank inequality gives actual matching-position count plus
remaining-row kernel rank. All old prime bits in Q are contained in
the discarded set, as proved by `source_primes_subset`. Q empty gives
the literal original quotient expression.

The actual match count is <=B*gamma(a,b)+3 outside the endpoint source
family. Combining the uniform residual and absorbing finite constants
proves, for every epsilon>0,

    delta_Q <= (gamma(a,b)+epsilon)*L.

This is `TargetQuotientRank.bounded_affine_rank` before geometric
encoding, and `AlignedTargetRank.uniform_core` after its construction.
No position count is equated with rank loss, and no absent old value
contributes a match.

## Literal counts, orientations and actual compatibility

For one fixed actual source parameter, every geometrically aligned
target lies in the explicit decoded pool. Its size is at most

    6*a*B^15.

The literal endpoint source family is independent of target choices.
After adjoining its reversed pairs, its size is at most

    (12*(a+b)+4)*B^7.

`AlignedTargetSourceTheorem.uniform_source_bounds` obtains the actual
source representation and covers both orientations, using the proved
symmetry of the actual quotient deficiency. It gives the rank conclusion
for all deterministically separated targets, without an affine event
assumption on the source. This proves the scope required by T1.11.

`compatible_of_source` obtains separation from a positive actual triple
joint event with a distinct target. Thus `uniform_both` also covers
the original compatible-target scope of T2.6. All old prime bits are
included in both versions. A single critical-band threshold precedes
all source pairs, all target choices and all prime-coordinate subsets.
The fixed channel a,b, fixed width D, critical-band width C and positive
epsilon are chosen before that threshold.

## Exact coefficient and numbered wrappers

`companion_T2_6` combines this actual geometric rank conclusion with
the proved gamma(a,b)<=2/3. `companion_T1_11` covers both leading
channels with the exact coefficients gamma(2,3)=1/3 and gamma(3,4)=1/2,
without source affine compatibility. Source privacy and local regularity
are unnecessary for the stronger one-unit statement.

The exact 8:9 attainment concerns the finite coefficient gamma; no
rank or Palm optimality is inferred from that computation. Source mass,
Palm mean and the principal Poisson approximation are separate unfinished
results. No external mathematical hypothesis, new Paper C port,
manuscript revision or Palomar registration is introduced.

## Historical checkpoints

The coefficient, actual matching, bounded-affine dyadic and finite rank
checkpoints remain in their original alignment documents, explicitly
labelled as historical. Their validation commits remain in the JSON
ledger. This complete proof extends improvements P1-MATH-0040 and
P1-MATH-0041 rather than adding artificial finding counts.

Validated complete T1.11/T2.6 (9,309 build jobs; 3,344 audited declarations;
1,059 directly checked coverage/finding names):
[3cc9dc9f816193e9488d32fab93f7aae9f9b6f90](https://github.com/Vulkin-prog/paper-p1-lean/commit/3cc9dc9f816193e9488d32fab93f7aae9f9b6f90).
