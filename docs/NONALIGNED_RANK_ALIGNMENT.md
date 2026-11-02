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

The integer-polynomial input is now derived from the field-polynomial
input by the proved actual rationalization/localization bridge. The
strongest source theorem therefore uses the same single field input
as conditional13.5. BCN and its geometric presentation remain open. No global axiom,
assumed target rank bound or hidden external theorem is introduced.
Article13.6 is now conditional;13.4 remains in progress and13.5
conditional. Proved coverage76/167 (main28/73, companion48/94),
confirmed findings80. No added Paper C source, dependency download,
manuscript-byte change or Palomar registration.

## Validation

Lean v4.36.0-rc2 full build passed (10545 jobs); the actual axiom audit passed for all5956 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All3673 distinct ledger/finding declarations were directly checked. All138 original manifest entries and167 numbered records are intact. Ubuntu available space:15.88 GiB. The actual critical short basis, support floor q=floor(B^b), common-curve point threshold, degree<=48q, degree-one exclusion, real grid rank budget, sublinear degree loss and final contradiction are kernel-checked. The actual finite nonaligned-pair maximum, literal Filter.limsup bound and a fixed sigma<1/2 before every C retain the ordinary explicit integer-polynomial BCN input. The numerical threshold<1/2 is unconditional. BCN and its rational/Gauss/geometric presentation specialization remain unformalized. Article13.6 is conditional; proved coverage76/167 (main28/73, companion48/94), confirmed findings80 unchanged. No added Paper C source, dependency download, manuscript-byte change or Palomar registration.


## Proved field/integer bridge

The integer-to-rational presentation bridge is now proved.
`IntegerCurveRationalization.coefficientMap` is the literal nested
coefficient ring map. An injective coefficient map preserves actual
total degree and the entire actual finite integer grid. Every unit
of a nested polynomial ring over a domain has total degree0.

The rational nested ring is constructed as two successive polynomial
localizations of the integer nested ring at nonzero integer constants.
An actual irreducible integer polynomial is prime in that UFD. Its
image is nonzero by coefficient injectivity and is not a unit because
its positive total degree is preserved. The pinned localization prime
mapping theorem therefore proves actual rational irreducibility.
No primitive-content, Gauss-bridge or irreducibility conclusion is
assumed. The field input applied at K=Q now gives the exact integer
input, with identical c,kappa,D,H and actual grid cardinality.

`NonalignedRankFieldBCN` consequently proves the full uniform rank
bound, literal source limsup and uniform strict half-window gap from
the same single `PlaneCurvePointCount.UniformBound c kappa` argument
already used in13.5. The integer input is a proved specialization of
that field input, not a second independent unformalized assumption.
BCN itself and the geometric-to-plane-polynomial theorem presentation
remain unformalized.13.4 stays in progress;13.5 and13.6 stay
conditional. Proved coverage76/167, confirmed findings80 unchanged.
No new Paper C source, dependency download, manuscript-byte change or
Palomar registration. One additional pinned Mathlib localization
module was compiled locally from existing sources.

Lean v4.36.0-rc2 full build passed (10551 jobs); actual axiom audit passed for all5965 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All3682 distinct ledger/finding declarations were directly checked. All138 original manifest entries and167 numbered records are intact. Ubuntu available space:15.87 GiB. The actual nested coefficient map preserves total degree and every integer grid. Two actual polynomial localizations, actual coefficient injectivity and the total-degree nonunit obstruction prove rational irreducibility of every positive-degree irreducible integer nested polynomial. The integer BCN input is derived from the field-polynomial input with unchanged c,kappa,D,H and actual grid cardinality. Full13.6 rank, actual maximum, limsup and strict half-window gap now use the same single field-polynomial BCN argument as13.5. No independent integer/Gauss bridge assumption remains. BCN itself and its geometric presentation remain unformalized;13.4 is in progress,13.5 and13.6 conditional. Coverage76/167 (main28/73, companion48/94), findings80. No extra Paper C source, dependency download, manuscript-byte change or Palomar registration.
