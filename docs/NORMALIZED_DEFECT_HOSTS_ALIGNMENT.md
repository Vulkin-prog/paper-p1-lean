# Actual exceptional normalized hosts and rational-unit weight bounds

This preparatory checkpoint now feeds the complete
[companion T2.5 proof](FIXED_CHANNEL_MASS_ALIGNMENT.md), including both
actual mass assertions and the literal real-cutoff separated family.
Statements of remaining fixed-channel work below describe this earlier
checkpoint. The complete main article 3.3 pair profile remains in progress.

This extends the quantitative source-count work in P1-MATH-0044 and
prepares article 3.3 and companion T2.5. The actual host counts and
rational-unit weight bounds are proved. Their final combination into
the retained private-channel mass and its phase equivalents remains open.
Neither numbered result is newly counted complete.

## Exact cutoff condition on actual distinct values

`NormalizedPrivateDefects.privateAbove_iff_nondefective` treats an actual
finite set S whose distinct values are at distance less than an integer H.
The existing `GoodEdgeCompression.PrivateAbove` condition above H is
equivalent to every value being H-nondefective. A nonzero odd prime
coordinate above H cannot occur at another value: such a prime cannot
divide their smaller nonzero distance.

For a true normalized union U=b*V_x union a*V_y with a<=b and an actual
exact unit, `normalized_dist_bound` gives distance <=2bL. Thus any
H>=2b(L+1) gives the exact equivalence on U, not just a sufficient
condition. `normalized_bad_witness` extracts an actual defective value
from the failure of the actual cutoff-private condition.

## Actual bad source pairs and explicit finite count

`NormalizedDefectSources.badSources` contains the actual dyadic ordered
source pairs with at least one exact unit and without cutoff privacy.
No probability or rank bound is imposed on this family.

Fix the initial unit indices i,j, a normalized vertex index k and one
of the two windows. Its actual normalized value is b*label_x(k) or
a*label_y(k). `value_injective` proves that this value determines both
centres on the literal source-pair set. Every value is positive for
N>=2 and is at most b*(2N+L).

Each corresponding defective source family therefore injects into the
actual positive H-defects below b*(2N+L). There are exactly 2B^3 choices
of i,j,k and window, where B=L+1. A finite union bound gives

    #badSources <= 2B^3 * #positiveDefectsBelow(H,b*(2N+L)).

The proof uses actual normalized values and actual source indices;
no assumed number of exceptional source pairs is an input.

## Fixed-channel square-root rate

`NormalizedDefectSourceCount.bad_sources_rate` combines this finite
injection with the already proved global defect estimate and absorbs
the polynomial factor. For fixed positive a<=b, fixed natural D,
critical-band width C and every epsilon>0, one threshold precedes all
lengths L and all integer cutoffs satisfying

    2bB <= H <= DB.

Above that threshold,

    #badSources <= N^(1/2+epsilon).

The constants and threshold can depend on the fixed channel and D.
This assertion does not extend the cutoff bound DB to growing b or D
after the threshold.

## Weights without privacy

`UnitFourierWeight.abs_signed_unit_sum` proves for every actual unit set

    |signedUnitSum| <= 2^((u-1)_+) - 1.

The proof counts nonzero elements of the actual even unit coefficient
space and bounds each binary sign by one. It requires no private
coordinates and no joint compatibility. Zero or one unit gives a zero
signed sum.

For positive coprime coefficients and positive centres, the already
proved actual unit count yields

    (u-1)_+ <= B/b,
    |signedUnitSum| <= 2^(B/b).

These bound the rational-unit contribution that is removed on bad hosts.
They do not assert that the full covariance of a nonprivate pair equals
the rational-unit sum.

## Source geometry and the baseline

`FixedChannelSourceGeometry` proves that a fixed initial unit choice
has at most N dyadic source pairs: its first centre determines the
second. Therefore all hosts with at least one unit have count <=B^2*N.
This polynomial baseline count suffices for the later required error
scale; no sharper NB estimate is asserted at this checkpoint.

Under N>(a+b)B, positive reduced a<b and N>=2, an actual source unit
also forces x+L<=y. This separation is deterministic and uses no event
compatibility. The existing source-order result gives x<y as well.

## Remaining mass calculation

The actual private-pair probability formula and complete dyadic signed
unit aggregate are now combined with these estimates. The subsequent
[actual mass reduction](PRIVATE_CHANNEL_MASS_ALIGNMENT.md) proves exact
bad-term deletion, the literal baseline and an explicit finite mass error.
The critical-scale comparison and positive fixed-channel phase equivalent
remain unfinished. The full pair profile also has its other arithmetic
regimes unfinished.

No new literature premise, Paper C port, manuscript revision or Palomar
registration is introduced. Original manuscript bytes are unchanged.

Validated actual normalized exceptional-host checkpoint (9,379 build jobs;
3,525 audited declarations; 1,240 directly checked coverage/finding names):
[bd95627543139b4690c1311ce84f622d8ce7a221](https://github.com/Vulkin-prog/paper-p1-lean/commit/bd95627543139b4690c1311ce84f622d8ce7a221).


## The actual nonprivate fixed-channel activity

Every actual pair joint mass is now bounded by
p_nominal^2*2^(full pair loss), without regularity or affine compatibility.
The proof uses the complete actual tuple rank, including its zero-mass
branch, and the exact identity rank+full_loss=2L. Every fixed rational
channel a:b, a<b, now has individual actual joint and absolute centered
weights at most N^(-2+1/b+epsilon) on all exact-unit source pairs. The
uniform aligned residual rank theorem supplies the missing nonprivate
rank factor. Heterogeneous marginal caps retain irregular and zero sites.

For the literal badSources family whose normalized union is not private
above H, the already proved N^(1/2+epsilon) count therefore gives both
unordered joint mass and absolute centered activity at most

    N^(-3/2+1/b+epsilon),

uniformly for critical lengths and 2b(L+1)<=H<=D(L+1), with a,b,D fixed
before N. This is the normalized-defect contribution used in T7.1; for
b>=3 it is smaller than N^(-1+epsilon). No disjointness of normalization
representations is assumed: image sums are bounded by positive source
sums, retaining every probability-zero pair. The proof is unconditional.

T7.1 and main 3.3 stay in progress: the regular macroscopic nonaligned
sector, full rational-channel classification and complete signed pair
profile remain open. Coverage stays 77/167 (main 28/73, companion 49/94),
confirmed improvements 94. This checkpoint proves an existing source-scale
contribution and introduces no new mathematical correction, external
premise, axiom, dependency download, original-source change or Palomar
registration.

Verified under Lean v4.36.0-rc2: full lake build (10985 jobs), source and ledger checks, actual axiom audit of 6967 declarations (only propext, Classical.choice and Quot.sound), and 4684 direct ledger/evidence declaration checks; Ubuntu root free space 15.13 GiB. Original manuscript bytes and all 167 statement hashes preserved.
