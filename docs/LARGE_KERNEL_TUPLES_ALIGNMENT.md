# Large-kernel branch of companion T1.14

The actual large-selected-kernel tuple count is proved. Companion T1.14
remains **in progress**: the all-small-kernel branch and the full compressed
fixed-width extension are not proved by this checkpoint.

Source: `companion_sections/arithmetic_appendix.tex:1035`, page 17,
`p1:arith:fixed-support`, statement hash
`a6cc454365ad3be4f4e5fd085e0de49e402d933a1af003488cdc040d20ed7d4b`.

## Actual configurations and finite receiver cost

`SeveralSelectedKernelWitness.AnchoredRelation` is an actual binary
prime-parity relation among the B values of an anchor window and the B
values of each of an arbitrary finite family of receiver windows. The
anchor has a specified selected value. Every prime above B in that
value's odd support must divide some receiver value: privacy inside
the anchor window excludes cancellation there. Evenness and separation
are unnecessary for this conclusion.

Each actual support prime is assigned once to one receiving block and
one offset. For m receivers there are at most (m*B)^#support assignments.
The existing prime partition gives pairwise coprime group moduli K_j
whose product is the actual kernel K. Each K_j divides K<=3N, including
empty groups with K_j=1. The finite residue fibre therefore satisfies

    #receiver tuples <= product_j(1+N/K_j) <= 4^m*N^m/K.

`SeveralKernelReceivers.receiving_card` proves this for each actual
assignment, retaining the additive terms. `hits_card` sums over all
assignments. This gives a complete finite proof of the source's
O_r(N^(r-1)/K) CRT cost, also when an individual group modulus exceeds N.

`WeightedReceiverKernelTail` generalizes the preceding T1.6 weighted
sum to assignment factor (m*B)^omega(K). With c_tau=2^tau/tau,

    weightedTail_m(B,X,T) <= sqrt(X)*T^(-1/2+tau)
      * exp(2*sqrt(B)+m*c_tau*B^(1-tau)).

The proof uses the actual canonical odd supports and a finite rough
Euler product. No counting or asymptotic estimate is an input premise.
For fixed m the extra exponential remains uniformly subpolynomial
under B<=D*log(N).

## All choices of the marked anchor

`LargeKernelTuples.tuples` contains actual (m+1)-tuples of dyadic starts
with a binary relation and a nonzero coefficient at a value whose
actual B-kernel exceeds T. The equivalent literal predicate is
`mem_tuples`. Every complete-window label is g(k)-1+i, including the
predecessor. The family includes non-even selections, repeated centres
and overlapping windows, so it also bounds separated even selections.

An actual marked anchor a is split off using Fin.succAbove. The
`encode` map to an anchor/receiver configuration is proved injective;
the full parity sum is split at a. There are m+1 choices of a, giving

    #tuples <= (m+1)*#anchored configurations.

For fixed m,C, 0<tau<=1/2 and epsilon>0,
`LargeKernelTupleCounts.tuple_count` proves one threshold before all
critical lengths and all real T>0, with

    #tuples <= N^(m+1/2+epsilon)*T^(-1/2+tau).

For s>=2 let beta_s=(2s-1)/(2s+1). `beta_bounds` proves
7/12<beta_s<1 and `exponent_identity` proves the exact exponent identity.
Choosing tau=min(1/4,epsilon/(4*beta_s)) after epsilon and using an
internal epsilon/2 margin gives `large_branch`:

    #tuples at T=N^beta_s <= N^((m+1)-2s/(2s+1)+epsilon).

Both the parameter choice and the error absorption are proved. This
establishes the source exponent for its large-selected-kernel branch,
without assuming a target tuple bound.

## Remaining scope and provenance

The all-small-kernel branch requires the two-small-kernel estimate in
T1.13/T1.5, including its coefficient-uniform determinant input. That
estimate is not supplied as a hidden hypothesis and no full T1.14
coverage is claimed. General subsets, fixed dilations and the complete
relative-image/source-family assembly remain to be connected.

These are new P1 proofs using the previously audited prime-assignment,
canonical-support, finite p-series and logarithmic-growth modules.
No new Paper C port, unproved literature input or manuscript revision
is introduced. The finite receiver constant and broader scope are
tracked as P1-MATH-0047. Numbered coverage remains 54/167.

The full build passed (9,441 jobs); the actual audit passed for all
3,655 theorem/lemma declarations, permitting only propext, Classical.choice
and Quot.sound. All 1,370 distinct coverage/finding declaration names
were checked directly by Lean. Original manuscript bytes are unchanged.

Validated large-kernel tuple-branch checkpoint (9,441 build jobs;
3,655 audited declarations; 1,370 directly checked coverage/finding names):
[8fa5f5d3988280093242c5b3fce68a506d9d1c80](https://github.com/Vulkin-prog/paper-p1-lean/commit/8fa5f5d3988280093242c5b3fce68a506d9d1c80).
