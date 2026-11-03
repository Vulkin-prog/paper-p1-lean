# Complete finite-order transfer to the full law, main15.13

Source: main_sections/exact_transfer.tex:887. The entire stated implication is proved under its exact254 fixed-order hypotheses and the already recorded geometric properties.

Main15.13 is now COMPLETE CONDITIONALLY as the literal theorem stated in
the source: for1<beta<=4/3, the254 fixed connected-activity estimates at
orders3 through256 imply the complete original-law quadratic estimate
with rate N^(-beta+epsilon). The same three previously recorded geometric
counting properties remain explicit ordinary arguments for the already
proved all-pair deficit, pair activity and connected tail. No new
geometric counting property is introduced.

The SOURCE FIXED-ORDER ASSUMPTION is explicit and has not been discharged:
FiniteConnectedActivity254.Hypothesis C beta quantifies ONLY r=3,...,256.
For every such r and every positive accuracy it supplies a nonnegative
constant A_r and a threshold before all critical N,L, bounding the sum
of |c(I)| over ALL actual connected r-site families with compatible
nullity<=2L by A_r*N^(-beta+accuracy). The constants may depend on r,C
and accuracy, exactly as in the printed big-O hypothesis. It assumes
neither the desired law bound nor a growing-order activity bound.
This completion proves the stated implication; it is NOT recorded as a
proof of those254 activity estimates, main15.10, main15.14 or main1.1.

FiniteConnectedActivity254.uniform_weighted chooses the254 constants
and thresholds before N using a finite index type. Exact cardinality
filters cover every family of size3..256, and finite fixed weights are
absorbed with a smaller accuracy. There is then ONE threshold for the
entire finite range. PrimitiveConnectedGeometry proves that primitive
original families are connected and have compatible nullity<=L, so the
same hypotheses control primitive sizes3..256. The already proved
unconditional primitive tail supplies all larger sizes with power7/5.
The complete primitive sum consequently has rate beta.

FiniteConnectedClosureUnderInputs combines the exact small-size estimate
with ConnectedTailUnderInputs at the literal cutoff from
SecondOrderBoundaryCutoff. The latter cutoff is proved o(log N). The
connected tail at sizesSTRICTLY GREATER THAN256 has power83/60, which is
strictly stronger than4/3. Every actual connected family of size3..K
and compatible nullity<=2L is retained, including incompatible systems.
Both the complete connected sum and all-cardinality primitive sum have
rate beta after one threshold, uniformly over every G in the full dyadic
ground. No unproved estimate at sizes>256 is added to the hypothesis.

The previous unconditional finite reconstruction theorem remains the
probabilistic mechanism. D2 contains direct original families and families
with exactly the nullity of a contained pair; ALL original pairs are
allowed. Its boundary has nullity<=2L. On D2, inverse centering is exactly
q(I)=product_I p_x+sum_pairs c(e)*product_complement p_x. The retained
polynomial differs from the full heterogeneous Bernoulli-plus-signed-pair
reference by the explicit discarded independent and pair terms. Failed
pair complements are proved non-direct after source compression. The
finite bound uses actual primitive centered mass, the actual all-pair
extension deficit, and exp(A2+T)-1-A2, with the whole linear pair activity
subtracted BEFORE the absolute component estimate. It holds for every K
and exact heterogeneous marginals, including zeros and incompatibility.

FiniteCompleteLawTransferUnderInputs uses a fixed internal accuracy
delta=min(epsilon/8,1/24). Absolute pair activity has rate2/3, the complete
connected remainder has rate beta>1, the all-pair independent deficit has
rate3/2, and the actual large-boundary mass has unconditional rate4.
The total component activity x is at most5*N^(-2/3+delta), hence eventually
at most1. The proved exponential remainder costs T+x^2*exp(x)/2. Its
squared pair term has rate4/3, so beta<=4/3 is exactly sufficient.
A uniformly bounded actual mean controls all free complements. Finally
the already proved signed heterogeneous Poisson--Charlier conversion
has rate5/3 and uses the EXACT actual mean and second factorial cumulant,
including the marginal diagonal. Fixed constants are absorbed before
taking the final threshold.

Parameters are a finite connected-tail bundle, a finite all-pair-deficit
bundle, and two finite-pair bundles for activity and conversion. At the
chosen delta, connected hypotheses use coarse margin delta/128 and
pair caps sizeCap(delta/32768), sizeCap(delta/1048576). The all-pair-deficit
hypotheses use caps sizeCap(delta/2048), sizeCap(delta/65536). Pair activity
and conversion use sizeCap(1/100). The underlying bundle definitions
expose every constituent ordinary surface cover, chosen-source surface
cover and normalized-curve bound. No BCN or bounded-moment assumption
occurs. All parameters, constants and fixed orders precede N; the final
threshold precedes ALL critical lengths and ALL dyadic subgrounds.

article_15_13 specializes the stronger subground theorem to the original
full count law. The source-count law is an actual normalized pushforward,
and the reference is the actual signed Poisson--Charlier measure; distance
is the convergent ordinary sum of absolute singleton differences. The
finite suffix count remains an actual positive kernel, never a freely
expanded signed approximation to a probability.

This completion adds3 modules,5 theorems,2 definitions and4 finite
parameter structures. Coverage is87/167 unconditional and31 conditional;
confirmed mathematical improvements remain146. This is completion of
the source implication and introduces no new correction identifier.
The optimal4/3 activity inputs and main15.14 reconstruction still require
their own proofs. No dependency download, original source-byte change,
Paper C port, hidden axiom or Palomar registration is introduced.

The main15.13 JSON row records the direct validation, previous unconditional finite checkpoint and exact proof commit.
