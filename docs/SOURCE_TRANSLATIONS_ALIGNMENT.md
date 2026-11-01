# Actual source translations — preparatory to fixed-channel mass

This preparatory checkpoint now feeds the complete
[companion T2.5 proof](FIXED_CHANNEL_MASS_ALIGNMENT.md), including both
actual mass assertions and the literal real-cutoff separated family.
Statements of remaining fixed-channel work below describe this earlier
checkpoint. The complete main article 3.3 pair profile remains in progress.

The exact translation-count step is proved. Article 3.3 and companion
T2.5 remain in progress; no additional numbered result is counted complete.
Source anchors preserved from V1.6:

- T2.5, page 22, `p1:arith:fixed-channel-mass`,
  `companion_sections/supplemental_arithmetic.tex:164`, hash
  `3f277bcb49753b0c57c75eaa012cdfc127c5f3253a66fb6fe0c40707b4e533e4`.
- Article 3.3, page 16, `p1:arith:pairs`,
  `main_sections/arithmetic.tex:162`, hash
  `2129f1e0418039211e95fa065f6ae434fe46849de797ea291acb0e08da94b412`.

## Exact integer interval, including predecessor offsets

For positive a<b<2a, offsets u,v with absolute values <=B and
N>=(a+b)B, define the integer parameter set

    ceil((N+u)/a) <= t < ceil((2N+v)/b).

`SourceTranslationInterval.ordered_bounds` proves that the omitted
other two dyadic inequalities are redundant at this finite scale.
`mem_translations` identifies membership with all four literal conditions

    N <= a*t-u < 2N,       N <= b*t-v < 2N.

Both signs of each offset are allowed, including the actual predecessor
offset -1. The endpoints use exact rational ceilings, not an informal
replacement of dyadic constraints by a limiting interval.

For rational alpha<=beta, the finite interval Ico(ceil alpha,ceil beta)
has cardinality within one of beta-alpha. Applying this and the offset
bounds gives the entirely finite estimate

    |card(translations)-N*(2/b-1/a)| <= B/a+B/b+1.

## Bijection with actual source pairs

For fixed actual source indices i,j in Fin(L+1), the existing literal
set `DyadicEndpointPairs.sourcePairs` consists of all dyadic pairs (x,y)
with b*label_x(i)=a*label_y(j). Coprimality gives a positive integer
parameter t with those labels equal to a*t,b*t.

`ActualSourceTranslations.translations_card` proves a bijection using
u=offset i and v=offset j. The forward map is the actual pair
((a*t-u).toNat,(b*t-v).toNat); dyadic positivity makes both conversions
exact. The inverse is extracted from the actual normalized equality.
The map is injective, so no multiplicity is silently dropped.

Thus the displayed interval error is an estimate for actual dyadic
source pairs at these fixed indices. It does not count the union over
all choices of source indices. A source with several exact units may
occur at several different choices, as it should in later relation-word
counting.

## Both orientations and the leading coefficient

For strict N>(a+b)B, every forward pair has x<y. Its reversed pair
family is disjoint from the forward family. `symmetric_card` proves
that their union has exactly twice the cardinality.

Write w(a,b)=2*(2a-b)/(a*b), exactly the source coefficient.
`symmetric_card_error` proves

    |card(both orientations)-N*w(a,b)| <= 2*(B/a+B/b+1) <= 6B.

The ordered error is <=3B. Both leading coefficients are exactly
w(2,3)=w(3,4)=1/3, so each leading channel gives N/3+O(B) translations
per fixed pair of within-window unit placements.

## One threshold before growing channel data

`SourceTranslationCount.uniform_counts` chooses one threshold before
all lengths and indices for each fixed channel. The stronger
`all_heights` chooses the threshold before every positive coprime
channel a<b<2a with b<=B^3, as well as every index choice.
It uses only the proved critical-band polynomial scale bound N>3B^4.
The finite errors remain 3B and 6B independently of the channel height.
`leading_counts` specializes to the two N/3 leading coefficients.

This stronger quantitative form of the translation step is recorded in
P1-MATH-0044. The [finite selection and signed-sum calculation](FINITE_CHANNEL_SUMS_ALIGNMENT.md)
was proved at the preceding checkpoint.

## Remaining mass argument

The later [weighted canonical-pattern checkpoint](CHANNEL_WORD_HOSTS_ALIGNMENT.md)
sums the actual translations with their predecessor signs, retaining main
term N*w*S and error <=6B*U. Identification with the actual complete
unit-relation/Fourier contribution and joint probability on private
normalizations, exclusion of defective normalizations, the
full fixed-channel mass and complete pair profile remain open. These
translation counts alone do not establish any of those assertions.
No new external mathematical hypothesis, Paper C port, manuscript revision
or Palomar registration is introduced.

Validated actual translation checkpoint and P1-MATH-0044 (9,323 build jobs;
3,394 audited declarations; 1,109 directly checked coverage/finding names):
[fc4c31d1a01ccb880d28fa6cdbd1d30040e054df](https://github.com/Vulkin-prog/paper-p1-lean/commit/fc4c31d1a01ccb880d28fa6cdbd1d30040e054df).
