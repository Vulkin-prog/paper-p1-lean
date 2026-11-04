# Corrected coarse asymmetric weighted profile

Source: companion T1.10, arithmetic_appendix.tex:811-860. Uses the [actual graph and target budget](ASYMMETRIC_TARGET_BUDGET_ALIGNMENT.md), [actual geometric host counts](ASYMMETRIC_COMPONENT_COUNTS_ALIGNMENT.md), and [unconditional sparse support](ASYMMETRIC_SPARSE_SUPPORT_ALIGNMENT.md).

The corrected asymmetric weighted profile is now bounded by
N^(4/3+epsilon), under the existing explicit geometric properties.
This is a COARSE profile bound, not the sharper31/24 target of T1.10.
It excludes CompressedTargetAlignment.Aligned Dold at the original
centres, as required by the confirmed scope correction P1-MATH-0162.
The old rule is arbitrary inside distance Dold*B of each centre.
The original new window has length B=L+1 and the original parity cutoff
is H, with (2*Dold+1)*B<=H<=Dcut*B. No old evenness, old independence,
selected-new independence or counting of old-set choices is assumed.

AsymmetricTargetComponents first identifies the genuine target component
population of the actual augmented graph. Every isolated free target
component supplies an actual new defective value. A finite injection
bounds their count by the number of defective original-window indices.
The exact loss therefore satisfies delta*<=D_new+c, where c counts the
actual nontrivial augmented-unpinned components meeting the new window.

AsymmetricSingletonBudget splits the singleton-target components into
isolated components, degree-(a,1) components for 1<=a<=K, and components
with at least K+1 actual old vertices. Their disjoint old-root sets lie
inside the actual interval [x-R,x+R], so the last population is at most
(2R+1)/(K+1). This counts actual old vertices and incurs no enlarged
envelope cost. If each small degree type has at most k components, then
c1<=D_new+K*k+(2R+1)/(K+1). All these finite statements are unconditional.

AsymmetricDefectDensity proves uniformly that D_new<=epsilon*B, using
the actual new interval and the existing local-defect estimate. The
cutoff is10(H+1), still a fixed multiple of B in the stated regime.
AsymmetricKernelPowers turns the finite budgets into actual powers:
globally2^delta*<=N^(1+epsilon); if c<=eta*B then
2^delta*<=N^(eta+epsilon); outside the small degree-one exceptional
populations,2^delta*<=N^(1/2+epsilon). In the last statement K is fixed
BEFORE k, the geometric properties, and the original data.

AsymmetricDenseMassUnderInputs combines the genuine geometric host counts
with these powers. Hosts with at least eta*B nontrivial components have
total weight sum2^delta*<=N^(1+epsilon). The small degree-one exceptional
hosts have N^epsilon count and the universal power N^(1+epsilon).
The remaining dense hosts have N^(1/2+epsilon) count and
N^(1/2+epsilon) power. The source surface cover, ordinary surface cover
and normalized curve-count properties are explicit arguments; none is
replaced by an assumed component count or weighted profile.

AsymmetricCoarseProfileUnderInputs defines the literal nonaligned
population, weight2^delta*-1 and total profile. It splits by the ACTUAL
component count at eta*B. The sparse sector uses the unconditional
N^(4/3+epsilon) support count and the N^epsilon power. The dense sector
uses the preceding N^(1+epsilon) weighted estimate. Contributions of
zero loss vanish exactly. The result is the full corrected coarse
weighted profile N^(4/3+epsilon), uniform over every prescribed old rule.

T1.10 remains in progress: the sharper corrected31/24 bound is not proved.
The printed radius-one statement remains false. No claim is made that
the new coarse estimate already closes the main optimal cumulant bound;
the compressed-centre comparison still needs a proved bridge. Coverage
stays87/167 unconditional and48 conditional. Findings stay161 improvements
plus the one confirmed statement-scope correction. No original manuscript,
dependency, toolchain or Palomar record changes.

The result ledger records exact verification and proof commits.
