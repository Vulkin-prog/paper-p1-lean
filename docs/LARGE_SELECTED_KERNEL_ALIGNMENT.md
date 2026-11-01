# Complete companion T1.6: actual selected large kernels

Both conclusions of companion Lemma T1.6 are proved by
`LargeSelectedKernelTheorem.companion_T1_6` under Lean v4.36.0-rc2.

Source: `companion_sections/arithmetic_appendix.tex:416`, page 9,
`p1:arith:anchor`, original statement hash
`82f3cf8921022846060a505c8fe8b23bb46ba877387589ffe277a885aacc0ff6`.

## Actual families and quantifiers

`SelectedKernelSourceFamilies.separatedPairs` consists of the ordered
dyadic pairs satisfying x+L<=y or y+L<=x and possessing nonempty actual
selected subsets of both complete windows whose rational product is a
square, with a selected value's actual B-kernel larger than T, B=L+1.
Both source orientations are included. The complete labels are
x-1+i, i in Fin B, including the predecessor. The smaller-kernel family
`smallWindows` consists of actual dyadic starts having at least one
complete-window value whose B-kernel is at most T.

The mixed-square family permits odd as well as even selections: the
proof establishes this stronger bound and in particular covers the
paper's even-selection square-class relations. The finite intermediate
family `LargeAnchorPairs.bothPairs` also permits overlapping windows;
the source separated family is proved to be its subset. No independence,
rank, regularity, affine compatibility or positive joint mass is assumed.

For every fixed critical-band width C, fixed 0<tau<1/2 and epsilon>0,
one threshold N0 precedes all N>=N0, all lengths with
|L-log(N)/log(2)|<=C, and every real 1<=T<=3N. The actual source bounds are

    #separatedPairs <= N^(3/2+epsilon) * T^(-1/2+tau),
    #smallWindows   <= N^(1/2+epsilon) * T^(1/2).

`uniform_source_counts` proves the same conclusion for every real T>0,
without the upper cutoff, and permits tau=1/2. The threshold remains
independent of T. The general arithmetic estimates only need a
logarithmic width cap rather than a critical-band lower bound.

## Finite argument and explicit constants

The actual odd support splits n uniquely into a positive square part,
a squarefree support of primes at most B and the support of its actual
large odd kernel. `KernelSupportFibres.weighted_fibres` reindexes any
nonnegative support weight by this canonical triple and then enlarges
to candidate supports with the exact fibre size sqrt(floor(X/(cr))).

For each prime above B in a selected anchor's odd support, the vanishing
mixed parity coordinate forces a divisible value in the other window.
`SelectedKernelWitness.other_prime_divisor` proves this directly; a prime
above B cannot divide a different value of the anchor window. This step
does not require even selections. Assigning the primes to the B offsets
gives at most B^#support possibilities. Differences of two solutions
are divisible by the product of the distinct primes, so each assignment
has at most floor(N/r)+1 other starts. Since r<=3N,

    floor(N/r)+1 <= 4N/r.

`KernelAssignments.hits_card_real` proves this also for r>N; no
unjustified removal of the additive term occurs. The two orientations
and B possible anchor placements give

    #bothPairs <= 8*B*N * weightedTail(B,3N,T).

For c_tau=2^tau/tau, `WeightedKernelTail.weighted_tail_exp` proves

    weightedTail(B,X,T) <= sqrt(X)*T^(-1/2+tau)
      * exp(2*sqrt(B)+c_tau*B^(1-tau)).

Here `PowerSeriesTail.constant (1+tau)` is exactly c_tau.
`SupportRankinTail.support_tail_le` supplies the finite Rankin step,
and its rough Euler bound uses the already proved integer p-series tail.
Only the finite prime pool up to X is used; an infinite Euler-product
identity is unnecessary.

The resulting finite estimates, for 2<=N and 1<=B<=N, are

    #bothPairs <= 8*sqrt(3)*B*N^(3/2)*T^(-1/2+tau)
      * exp(2*sqrt(B)+c_tau*B^(1-tau)),
    #smallWindows <= 2*sqrt(3)*B*N^(1/2)*sqrt(T)*exp(2*sqrt(B)).

The second estimate follows from the proved square-root endpoint of
`RankinSmallKernel.rankin_half` and a literal placement cover.
`LogPowerExponential` proves exp(K*B^q)=N^o(1) uniformly for
B<=D*log(N), fixed 0<=q<1 and nonnegative K,D. Combining it with the
existing square-root exponential and logarithmic placement bounds
gives both asymptotics without a T-dependent threshold.

## Provenance and scope

The canonical-triple argument is adapted and generalized from
`PaperC/Arithmetic/LargeKernelWeightedCounting.lean`, commit
`b9fa9ba490f201b408a302a86f1594ee620b228b`, Git blob
`0a767c88c4899fbb1fc4996c6a5188a5c19af103`, Apache-2.0.
Its arbitrary-weight generalization and all P1 bridges are rebuilt under
the pinned new compiler. No old compiled artifacts are reused and no
new unproved literature estimate is introduced.

The explicit finite version and stronger selection scope are tracked as
P1-MATH-0046. Main article 3.2 and the complete pair profile 3.3 still
require the other small-kernel and nonaligned geometric regimes. This
checkpoint does not prove those results or authorize a Palomar submission.

Validated complete companion T1.6 checkpoint (9,427 build jobs;
3,626 audited declarations; 1,341 directly checked coverage/finding names):
[3be7415366bd3d27aa016bf9690b0f93d7304fd9](https://github.com/Vulkin-prog/paper-p1-lean/commit/3be7415366bd3d27aa016bf9690b0f93d7304fd9).
