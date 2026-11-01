# Actual finite private-channel mass and direct deletion of bad unit terms

This records the finite-reduction stage of P1-MATH-0045. The subsequent
[complete T2.5 proof](FIXED_CHANNEL_MASS_ALIGNMENT.md) also closes the
critical remainder, positive phase and literal real-cutoff family.
Article 3.3 remains in progress beyond this fixed-channel input.

## Actual source family

`PrivateChannelSources.goodSources` consists of actual dyadic ordered
pairs with at least two exact units and the literal `PrivateAbove H`
condition on every distinct value in b*V_x union a*V_y. It has no
positive-probability filter. Pairs of joint probability zero are retained.

For N>=2 and N>(a+b)B, the existing source geometry gives x<y and,
for positive reduced a<b, x+L<=y. Thus separation is proved from an
actual unit, rather than assumed or inferred from event compatibility.
The symmetric `channelSources` family is the union with the swapped
source family. `orientation_disjoint` proves their disjointness.

`forwardMass` and `channelMass` are literal sums of the actual
infinite-measure joint probability q_{x,y} over these finite families.
`channel_mass_twice_forward` proves M=2*forwardMass using the actual
swap bijection and symmetry of the two-element event.

## Actual private probability and baseline

For L>0, privacy derives both marginals p=2^-L. The previously proved
actual private pair formula gives

    q_{x,y} = p^2*(1+signedUnitSum(a,b,x,y,L)).

`forward_mass_formula` sums this exact formula. The constant term is
the literal number G of retained forward sources. The proved bound
G<=B^2*N is used at that strength; no sharper NB count is asserted.

## Exact deletion of nonprivate rational-unit contributions

Let F be the full dyadic forward sum of the actual signed nonzero
even-unit contribution. Let V be its sum over `NormalizedDefectSources.badSources`.
The zero/one-unit contribution vanishes, so the actual signed sum partitions
exactly into retained private terms and bad terms. This is
`PrivateChannelRemoval.signed_sum_partition`.

`bad_signed_sum_bound` uses the proved rational-unit weight bound,
without privacy or joint compatibility:

    |V| <= #badSources * 2^(B/b).

No complete covariance formula on a nonprivate pair is used. In particular,
no bound on its complete residual nullity is required to delete this
rational-unit contribution.

## Exact actual mass decomposition and finite error

`PrivateChannelMassBound.mass_exact_decomposition` proves

    M = p^2*(2F + 2G - 2V).

The [actual dyadic aggregate](DYADIC_UNIT_FOURIER_ALIGNMENT.md) already
gives |2F-N*w*S|<=6B*U. Combining that estimate, the retained source
count and the direct bad-term bound yields `finite_mass_error`:

    |M-p^2*N*w*S|
      <= p^2*(6B*U + 2B^2*N + 2*#badSources*2^(B/b)).

This holds for N>=2, L>0, positive reduced a<b<2a and N>(a+b)B.
The integer cutoff H is unrestricted in this finite theorem. For the
later small exceptional-host count, the
[proved defect estimate](NORMALIZED_DEFECT_HOSTS_ALIGNMENT.md)
retains 2bB<=H<=DB with fixed channel and fixed D.

## Mathematical simplification and remaining asymptotics

The source removes defective pairs by their host count and a complete
pair-nullity estimate. The finite reduction above instead deletes
rational-unit terms before applying the actual private covariance
identity. Their own even coefficient-space cardinality gives the weight
bound directly. The residual-rank theorem is therefore unnecessary for
this finite fixed-channel mass calculation. It remains relevant to
other arithmetic regimes and rank conclusions.

The subsequent [critical mass rate](PRIVATE_CHANNEL_MASS_RATE_ALIGNMENT.md)
bounds U and compares these three actual errors on the critical scale,
giving the stronger explicit O(B^2/N) remainder and the source's
N^(-1+epsilon) estimate. The later
[complete T2.5 alignment](FIXED_CHANNEL_MASS_ALIGNMENT.md) proves the
positive phase and exact real-cutoff convention as well. The complete
main pair profile retains its other unfinished regimes.

No new literature premise, Paper C port, manuscript revision or Palomar
registration is introduced. Original manuscript bytes are unchanged.

Validated actual finite channel-mass checkpoint (9,385 build jobs;
3,538 audited declarations; 1,253 directly checked coverage/finding names):
[37e67975065e2b4df18be484c2e7ba9123a6c8b9](https://github.com/Vulkin-prog/paper-p1-lean/commit/37e67975065e2b4df18be484c2e7ba9123a6c8b9).
