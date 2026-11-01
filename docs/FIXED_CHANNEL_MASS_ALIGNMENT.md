# Complete companion T2.5: actual fixed-channel mass and positive phase

Companion Lemma T2.5 is proved, including both its mass asymptotic and
positive phase assertion, for the literal separated source family and
fixed real prime threshold. The declaration is
`FixedChannelMassTheorem.companion_T2_5`.

Source: `companion_sections/supplemental_arithmetic.tex:164`, page 22,
`p1:arith:fixed-channel-mass`, original statement hash
`3f277bcb49753b0c57c75eaa012cdfc127c5f3253a66fb6fe0c40707b4e533e4`.
The main article's complete pair-profile Theorem 3.3 remains in progress.

## Literal family and actual probability

The fixed reduced channel has positive a<b<2a; for integral coefficients
these conditions imply b>=3 and are the source's b/2<a<b domain.
Fix any real D>=2b and take the source threshold D*B, B=L+1.
This is an explicit sufficient choice of the source's fixed coefficient
C_{a,b}, chosen large enough for the normalized widths.

The canonical forward family has both centres in the actual dyadic block,
at least two exact units b*label_x(i)=a*label_y(j), and a private prime
coordinate above D*B on every distinct normalized value in b*V_x union a*V_y.
The reverse orientation is its swapped ordered copy. This makes the
source's symmetry convention explicit: the canonical normalization is
transported with the copy when the ordered centres are exchanged.

`RealPrivateChannelSources.separatedChannelSources` filters the symmetric
family by the actual separation predicate x+L<=y or y+L<=x. Its mass is
the literal sum of actual infinite-measure joint probabilities q_{x,y}.
There is no positive-probability filter: zero-probability pairs remain,
as required by the source.

`real_sources_separated` derives this separation deterministically from
an actual source unit once N>(a+b)B. `eventual_mass_eq` proves equality
between the literal separated-family mass and the earlier unfiltered
actual channel mass under one critical-band threshold. The family
identification is proved rather than assumed.

## Exact real-threshold convention

For nonnegative real H, `privateAbove_floor` proves that a prime p>H
is exactly a prime p>floor(H). The literal real-cutoff family is therefore
equal to the actual integer-cutoff family at floor(D*B).
`cutoff_bounds` proves

    2bB <= floor(D*B) <= ceil(D)*B.

The previously proved defect-host counts, finite mass identities and
rate bounds apply with fixed natural ceil(D). This does not replace
the manuscript's real threshold by a different family.

## Exact signed sum and positive leading behavior

The actual word and dyadic-source bijections identify the signed main
sum with the source's exact S_{a,b}(L), including its Euclidean remainder,
empty cases and diameter-L contact signs.

For m>=1, `SignedChannelLeadingBounds` rewrites the exact finite identity
with r=L mod b and m=floor(L/b) and proves the following coefficient bounds:

    S = 2^(m-1)*(A*m+T)-P,
    1 <= A <= 2b^2,     0 <= T <= 6b^2,
    0 <= P <= 5b^2*m.

For L>=10b^3 it proves the explicit finite bounds

    L*2^m <= 8b*S,
    S <= 4b*L*2^m,
    S > 0.

These hold for every positive a<b. No sign of S is inferred from an
unsigned bound, and r is not discarded or assumed fixed.

`CriticalChannelPowers` gives both-sided critical bounds on the nominal
square probability and the actual quotient word power. With the positive
dyadic coefficient w=2*(2a-b)/(a*b), `ChannelMainTermBounds` proves
positive lower and upper constants times L*N^(-1+1/b) for p^2*N*w*S.

## Actual mass error and positive phase

The [finite mass reduction](PRIVATE_CHANNEL_MASS_ALIGNMENT.md) deletes
bad rational-unit terms before applying the private covariance identity.
Their weights are bounded directly, without complete residual-nullity
control. The [critical remainder](PRIVATE_CHANNEL_MASS_RATE_ALIGNMENT.md)
is the stronger explicit estimate

    |M-p^2*N*w*S| <= K(C,b)*B^2/N,
    K(C,b)=(2^C)^2*(8*2^((C+1)/b)+2)>0.

`FixedChannelMassTheorem.strong_error` proves this for the literal separated
real-cutoff family. `source_error` gives, for every epsilon>0, a larger
threshold with

    |M-p^2*N*w*S| <= N^(-1+epsilon).

`PrivateChannelMassPhase` shows the error is eventually at most half
the positive main-term lower bound. Its real-cutoff transport,
`source_positive_phase`, gives positive constants c,k and one threshold
such that

    c*L*N^(-1+1/b) <= M <= k*L*N^(-1+1/b).

These are both assertions of source T2.5. Every threshold precedes all
lengths in the fixed critical band. The channel and real cutoff coefficient
are fixed before the threshold. No growing-channel phase uniformity is
asserted here; the separate signed aggregate estimate through height B^3
retains its own earlier scope.

## Improvements and project scope

P1-MATH-0043 now includes explicit positive finite signed-sum bounds.
P1-MATH-0044 supplies actual source counts, real-cutoff transport and
exceptional normalized hosts. P1-MATH-0045 simplifies the fixed-channel
mass proof and strengthens its remainder to O(B^2/N). The proved baseline
count is B^2*N; the sharper source NB intermediate count is not claimed.

This completes one fixed-channel input to article 3.3. That theorem's
complete pair profile and other arithmetic regimes remain unfinished.
No new literature premise, Paper C port, manuscript revision or Palomar
registration is introduced. Original manuscript bytes are unchanged.
