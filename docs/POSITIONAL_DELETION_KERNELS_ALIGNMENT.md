# T19.10 preparation: actual deletion and isolation kernels

Source: companion_sections/limits_appendix.tex:641-749. The independent-background comparison and the full numbered proposition remain open.

CompanionT19.10 moves from NOT STARTED to IN PROGRESS. Uniform
one-edge deletion and isolation are now LITERAL probability kernels
on full configurations. Their actual original-model laws, pointwise
count costs, moment bounds and contraction of EVERY fixed polynomially
weighted field distance are proved. Applying the same operations to
both sides of main20.1 preserves its4/5 rate, with no new input or
exponent loss. The target at this stage is the SAME deletion applied
to the compound field. Comparison to the independent single-arrival
field, the finer intensity/covariance assertions and every sharp
O(a_N^2) conclusion remain open. No numbered completion is added.

PositionalMarkovKernel constructs the absolutely convergent mixture
sum_v coeff_v(nu)*K(v) for ANY probability kernel between two site
types, including signed inputs. The continuous linear map has norm
at most one, acts exactly on atoms, has the literal singleton-mixture
formula, preserves total mass and nonnegative coefficients, and sends
probabilities to probabilities. Ordinary L1 distance contracts.

PositionalKernelMoments proves nonnegative test transfer: if the
kernel g-moment at v is at most f(v), the output g-moment is at most
the actual input f-moment. All positive double-series summability
and summation orders are proved. PositionalWeightedKernel bounds
absolute output coefficients by the mixture of absolute inputs and
proves the analogous SIGNED weighted norm contraction. A weight
decreasing in expectation therefore contracts weighted distances.

PositionalDeterministicMap specializes these results to literal
pushforwards of configurations. Every count-decreasing map preserves
all fixed polynomial moment bounds. PositionalUniformAtoms constructs
the normalized uniform mixture of finitely many actual configuration
atoms and proves its exact sum for EVERY real test.

PositionalPairDeletion defines active edges, their incident vertices,
the endpoint vector, subtraction of one at each edge endpoint, and
isolation by zeroing all incident coordinates. For an active edge,
deleted+endpointVector is exactly the original field; a two-element
edge gives count Z-2. Both operations decrease total count, and
isolation leaves no active nonempty edge. For BINARY inputs the
original field is isolated field plus the incident-vertex indicator.
With k active two-element edges, their incident set has at most2k
vertices, and at least2 when k>0. Consequently

 isolatedCount<=W=Z-2*1_(k>0),
 W-isolatedCount<=k*(k-1).

These pointwise graph statements include k=0,1 and need no degree,
arithmetic, independence or compatibility assumption.

PositionalDeletionKernels chooses an ACTUAL active edge uniformly,
subtracts one at its endpoints and keeps the input unchanged if none
exists. Isolation is the actual deterministic pushforward. Both are
probability kernels and preserve all fixed polynomial moment bounds.
For every real count test, the once-kernel test sums exactly to its
value at Z-2*1_(k>0) when every candidate edge has two sites.
PositionalDeletionWeightedContraction proves both operations contract
EVERY fixed polynomially weighted distance, even for signed laws.

PositionalDeletedFields defines the original, once-deleted and
isolated laws from the ORIGINAL prime-sign cylinder. Probability
status is proved. A kernel applied to a finite field law is exactly
the weighted finite mixture of the kernel at each actual sample
configuration. This identifies the auxiliary uniform choice and
isolation with the intended original model. Every original
configuration is binary, so the count-cost bound applies pointwise
to every actual infinite prime-sign sample.

PositionalDeletionTransferUnderInputs gives UNCONDITIONAL subpolynomial
moments of every fixed order for both actual deleted fields, uniformly
over ALL dyadic subgrounds and ALL finite candidate edge populations
chosen after N. Its weighted comparison theorem transfers main20.1
to both transformed compound targets at the SAME4/5 rate and with
the SAME existing geometric bundle selected before the fixed degree.
It does not replace those targets by the independent background.

PositionalKernelCoupling proves an exceptional-event bound for two
probability kernels: if they agree away from B, except at zero input
coefficients, output L1 distance is at most twice the input mass of B.
Absolute convergence of the difference mixture is checked.

All finite probability, graph, kernel and moment statements are
unconditional. Only transfer of the arithmetic4/5 comparison retains
the existing explicit geometric inputs. No new external property,
axiom, finding, Paper C port, download, original source edit or Palomar
registration is introduced. Coverage stays87/167 unconditional and
45 conditional, with155 confirmed manuscript improvements.

The JSON row records the exact verification and proof commit.
