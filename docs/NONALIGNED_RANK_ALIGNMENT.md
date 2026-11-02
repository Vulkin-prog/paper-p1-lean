# Uniform nonaligned rank: complete reduction under explicit BCN

Source: article13.6, `p13:rig:nonaligned`, `main_sections/pair_rigidity.tex:259`. Status: **conditional**.

The complete actual nonaligned-rank argument is now proved under
the ordinary explicit integer-polynomial BCN input
`IntegerCurvePointInput.UniformBound c kappa`, with c>0. The source
BCN theorem and its specialization remain unformalized. This is a
conditional result and does not increase proved numbered coverage.

For every epsilon>0 choose the actual exponent

    a = exp(-3epsilon/8)/2,
    (2/3)log(1/a) = (2/3)log2 + epsilon/4,

and b=(a+1/2)/2, so a<b<1/2. The proved source short basis13.1 has
physical basis support at most2q for q=floor(B^b), once B is large.
The actual q satisfies1<=q<=B. All floor, logarithmic and power
estimates are proved. The critical geometry B<=U logN and the actual
budget q^2 log(B+1)=o(B) discharge the explicit common-curve threshold
(B+1)^(1000000q^2)<N.

If d_xy>((2/3)log2+epsilon)B, the extracted actual rank exceeds
epsilon B/2. Its actual common curve has D<=48B^b. The proved
degree-one branch gives literal source alignment when extracted
rank>=9 and x,y>B, so nonalignment forces D>=2. The actual grid
rank budget is

    rank <= #integerGrid + 1 + 6D^2.

The loss1+6D^2 is at most epsilon B/4 eventually. The named external
integer BCN input, through the proved growing-degree analytic
estimate, bounds that same actual grid by epsilon B/8. This gives
the contradiction. No compatibility assumption is used.

`critical_rank_bound` has one N0 before every length in the fixed
critical band and every actual dyadic pair. `nonalignedPairs`,
`maximalRank` and `maximalRatio` construct the actual finite maximum,
with value0 for an empty pair set. Its uniform bound and the literal
Filter.limsup inequality hold for every eventually critical length
function L(N). The numerical inequality(2/3)log2<1/2 is proved
unconditionally by rational power/log bounds. A single sigma<1/2
is chosen before every band constant C, giving a uniform half-window
gap under the same explicit external input.

The field-polynomial input used for conditional13.5 and the integer-
polynomial input here are separately named. Their rational/Gauss
presentation bridge has not been claimed proved. No global axiom,
assumed target rank bound or hidden external theorem is introduced.
Article13.6 is now conditional;13.4 remains in progress and13.5
conditional. Proved coverage76/167 (main28/73, companion48/94),
confirmed findings80. No added Paper C source, dependency download,
manuscript-byte change or Palomar registration.

## Validation

Lean v4.36.0-rc2 full build passed (10545 jobs); the actual axiom audit passed for all5956 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All3673 distinct ledger/finding declarations were directly checked. All138 original manifest entries and167 numbered records are intact. Ubuntu available space:15.88 GiB. The actual critical short basis, support floor q=floor(B^b), common-curve point threshold, degree<=48q, degree-one exclusion, real grid rank budget, sublinear degree loss and final contradiction are kernel-checked. The actual finite nonaligned-pair maximum, literal Filter.limsup bound and a fixed sigma<1/2 before every C retain the ordinary explicit integer-polynomial BCN input. The numerical threshold<1/2 is unconditional. BCN and its rational/Gauss/geometric presentation specialization remain unformalized. Article13.6 is conditional; proved coverage76/167 (main28/73, companion48/94), confirmed findings80 unchanged. No added Paper C source, dependency download, manuscript-byte change or Palomar registration.
