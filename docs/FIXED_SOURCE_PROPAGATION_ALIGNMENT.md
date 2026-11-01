# Main 6.3 — Complete conditional sums, propagation and exceptional mass

Source: main Proposition 6.3, page 22, `p1:fixed:propagation`,
`main_sections/fixed_moments.tex:105`, statement SHA-256
`a053ebcb00eb0a8b133d02a11c330ec2119e4122cb9304305b1a7b8e4858a659`.
The complete numbered result is **proved**, including the final
local-defect/contact positive-mass conclusion at every fixed order.

## Actual conditional affine probabilities

`WindowFamilyConditional.sourceEvent` is the literal event that all
source relative-bit vectors have their prescribed values under the
infinite prime-sign measure. `conditionalProbability` is the real
measure of the intersection with the target-vector atom divided by
the actual source-event probability.

`CompatibleWindowPrescriptions.source_mass_affine` transports every
source event to the finite joint affine system. Every positive-mass
prescription therefore has an actual cylinder witness. Homogeneous
prescriptions have positive mass. No compatibility or witness existence
is assumed without an explicit positive-mass source premise.

`WindowFamilyConditional.conditional_eq_mass` identifies the actual
conditional probability with the finite affine observation probability
after observing the full source row space. Its increment is proved
equal to the actual square-class delta_z, including overlapping,
dependent or repeated sources.

`ExtensionRankBudget.total_rank_identity` proves the exact total-rank
identity. `FamilyConditionalMass.kernel_rank_identity` combines it
with the quotient-rank identity. The conditional mass is either zero
or 2^delta times the inverse power of two of the actual target rank.
Nonnegativity and the cap one are proved from the actual events.
The critical local relation-rank bound <=1 then gives the uniform
upper bound 2*2^delta/2^L for every target prescription, even when its
unconditioned affine atom is incompatible.

## The complete conditional sum

`WindowConditionalSum.finite_bound` proves the exact low/high split

    sum_z conditional(z) <= N*(2/2^L)*2^(eta*L)
                              + # {z : delta_z>=eta*L}.

`SmallRankLossPower` proves an explicit critical-band power bound.
`FixedSourceConditionalSum.witness_sum` combines it with the complete
actual main 6.2 count. One eta is selected before every source tuple,
length and cylinder. The exponent margins and constant absorption
are proved.

`FixedSourceConditionalSum.conditional_sum` removes the witness
parameter using its constructed cylinder representative. It bounds
the actual infinite-measure sum by N^epsilon after one threshold,
for every compatible affine source prescription and arbitrary target
prescriptions, which may depend on the centre. Repeated sources are
allowed and all centres in I_N are counted. `homogeneous_sum` gives
the all-homogeneous specialization. `fresh_conditional_sum` proves
the exact source-excluding first display of main 6.3.

## Actual finite ordered extension families and mass propagation

`PrescribedTupleMass.joint` is the actual infinite-measure probability
of an ordered prescribed tuple. `conditional_factor` proves its exact
factorization when a target is appended. The zero-source-mass case is
proved from event inclusion, rather than divided by zero.

`TupleExtensions.step` and `more` construct the literal finite families
by appending centres from I_N. Membership of `more` is equivalent to
the initial source tuple belonging to the seed family and every centre
belonging to I_N. The exact sum over a step is a double sum over old
tuples and new centres. Distinct source tuples give disjoint extensions.
`distinctMore` filters actual injective tuples; `mem_distinctMore`
proves its full source-prefix, coordinate and distinctness description.

`FixedSourceMassStep.point_step` and `family_step` prove the actual
one-step mass bound using the completed conditional sum. `bounded_orders`
chooses one threshold for every source order in a fixed range.
`TupleMassIteration.iterate` proves the complete finite induction on
actual extension families. `FixedOrderMassPropagation.all_extensions`
uses the margin epsilon/(k+1) before every seed family and prescription.
It bounds the mass of all k-fold extensions by N^epsilon times the
actual seed mass, allowing repeated centres. `extension_subfamilies`
bounds every subfamily by nonnegativity.

`main_6_3_propagation` supplies the literal ordered-distinct extension
assertion, with r=s+k. `PrescribedRunMass.joint_eq_infinite` identifies
the prescribed start masses with the original infinite run moments.
`original_run_extensions` gives the exact source specialization. The
all-homogeneous specialization is already included by the arbitrary
common centre prescription. There is no assumed propagation estimate.

## Actual local-defect and exact-contact seed masses

`SingletonSeedMass` constructs the literal one-coordinate irregular
seed family and identifies its mass with the actual affine-window
atoms. `IrregularSeedMass` combines the proved local-rank and
irregular-population bounds to give O(N^(-1+epsilon)) seed mass,
uniformly for arbitrary affine prescriptions.

`ContactWindowSpan.value_union` identifies the two physical intervals
at exact contact. They share their boundary value. The complete finite
even-image union theorem proves

    S(x,L) + S(x+L,L) = S(x,2L).

`PrescribedTupleRank` identifies the actual prescribed tuple atom with
zero or the inverse power of two of its total effective rank. Thus
`ContactPairMass` bounds each exact-contact atom using the actual local
relation code of the union interval. Restriction to actual defective
positions bounds that relation rank. `ContactDefectBudget` applies
the complete local count at cutoff 2L+1 and diameter 2L.
`LogarithmicDefectPower` proves its binary factor is N^epsilon after
one uniform threshold. `ContactSeedMass` gives point mass
O(N^(-2+epsilon)) and total forward contact mass O(N^(-1+epsilon)).
`ExactContactSeeds` constructs the actual two-coordinate seed family
inside I_N and proves its coordinates, membership and mass bounds.

## All seed positions and the full original exceptional population

`TuplePositions.allPositions` is a literal finite permutation cover of
the actual distinct extension family. It costs at most r!, with a
proved weighted sum bound. The finite permutation extension theorem
constructs a permutation for every injected seed position.
`PrescribedTuplePositions.joint_permute` proves invariance of actual
joint mass. `PositionedMassPropagation` and `PositionedSeedBounds`
therefore propagate both actual seed families to every tuple position.

`BadSeedFamilies` defines the literal ordered-distinct populations
containing a local rank defect or a contact of distance at most L.
Strict contacts have zero mass for the original run prescriptions,
by deterministic run separation. Every positive contact therefore
has distance exactly L and contains an injected actual contact seed.
Filtering out zero-mass tuples preserves the full contact mass. This
strict-contact exclusion is not asserted for homogeneous overlapping
window prescriptions. Their conditional and propagation results
remain valid separately.

`FixedExceptionalMass` proves the local-defect and full contact bounds
for the actual finite populations, then their union. It includes the
small orders where a contact cannot exist. `bad_original_mass` is
stated directly with the original infinite joint run moments.
`FixedSourcePropagationTheorem.main_6_3` bundles all three source
assertions after one common threshold, with r=s+k. The order k and
all constants are fixed before N, L, prescriptions and seed families.

Coverage is 71/167 (main 25/73, companion 46/94), with 69 confirmed
independent findings. Main 6.4 and its moment expansion remain separate.
No external assumption, new Paper C code, original manuscript edit or
Palomar registration is introduced.

## Earlier conditional-sum verification history

Conditional-sum checkpoint verification: Lean v4.36.0-rc2 full build passed (9999 jobs); actual axiom audit passed for all 4908 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 2623 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 16.57 GiB. The first conditional-sum assertion of main 6.3 is complete on the actual infinite prime-sign measure, including arbitrary compatible affine prescriptions, homogeneous prescriptions and literal source exclusion. Extension-family propagation and the final seed consequence remain open, so main 6.3 stays in progress. Coverage and confirmed independent findings remain 70/167 and 69. No conditional-sum premise, external assumption, new Paper C port, manuscript-byte change or Palomar registration.

Validated conditional-sum proof checkpoint: [d61129a4481b626b35958ee0329ac668362aec1e](https://github.com/Vulkin-prog/paper-p1-lean/commit/d61129a4481b626b35958ee0329ac668362aec1e).

Fixed-order propagation verification: Lean v4.36.0-rc2 full build passed (10011 jobs); actual axiom audit passed for all 4929 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 2644 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 16.55 GiB. The conditional-sum and actual ordered-distinct extension-family propagation assertions of main 6.3 are complete, including an exact bridge to original infinite joint moments. The final local-defect/contact seed conclusion remains open; main 6.3 stays in progress. Coverage and confirmed independent findings remain 70/167 and 69. No propagation-mass premise, external assumption, new Paper C port, manuscript-byte change or Palomar registration.

Validated actual propagation proof checkpoint: [b9e411cecc036eaa1e87da5a2f981792d9aadc76](https://github.com/Vulkin-prog/paper-p1-lean/commit/b9e411cecc036eaa1e87da5a2f981792d9aadc76).

Complete main 6.3 verification: Lean v4.36.0-rc2 full build passed (10043 jobs); actual axiom audit passed for all 4978 theorem/lemma declarations with only propext, Classical.choice and Quot.sound. All 2693 distinct ledger/finding declarations were directly checked. All 138 original manifest entries and 167 numbered records are intact. Ubuntu available space: 16.50 GiB. The full conditional-sum, actual ordered-distinct propagation and all-position local-defect/contact mass conclusions are proved, with original infinite joint moments and one common threshold. Coverage is 71/167 (main 25/73, companion 46/94); confirmed independent findings stay 69. No conditional-sum, propagation, contact-rank or seed-mass premise, external assumption, new Paper C port, manuscript-byte change or Palomar registration.
