# Actual randomized clean-target cost and quarter-flip selection

Sources: companion T19.16 and T19.17, limits_appendix.tex:1214 and1313, including the clean-pair constructions in their proofs. All original source hashes are preserved in the numbered ledger.

Companion T19.17 gains the actual randomized clean-target cost
formula and a quarter-flip ordinary source choice, with an arbitrary
independent finite auxiliary probability. The global hybrid field,
source aggregation and final randomized obstruction remain in progress.

IndependentFiniteProbability constructs the literal product law from
arbitrary normalized finite real weights. It proves weighted Fubini,
both exact marginals and the uniform/weighted expectation interchange.
No uniformity or separate nonempty instance is imposed on the auxiliary
law. RawAuxiliaryObservation then derives the actual joint uniform
source/target word law with that independent auxiliary law from the
surjective original raw matrix. An assumed independent-word probability
law is not substituted for the original prime model.

RandomizedSourceFlip uses the actual correction

  delta_i(U,xi)=U_i+b_i+g(U,xi).

For any two different original source indices, their correction bits
sum to the original fair parity. The orientation may depend arbitrarily
on U and xi. Weighted finite expectation therefore proves that one
candidate has flip probability theta_i>=1/4. If the actual source has
two ordinary Q-smooth candidate indices, one such candidate is selected
among them. This local cost selection does NOT require fairness of g;
the fully private Palm law requires the separate fairness hypothesis
proved and scoped at P1-MATH-0189.

RandomizedCleanPivotWordCost connects this calculation to the actual
private prime modifications. A literal clean target contains the chosen
source prime to valuation one and contains no other changed source
prime in any target position. The actual target raw word then changes
by exactly single_0(delta_i(U,xi)). This is a pointwise identity for
every original prime sample and auxiliary draw. The actual source
template b+g(U,xi)*1 is used inside the original forceWord map.

For a clean target whose joint raw matrix is surjective, its actual
positive unsigned indicator-change expectation satisfies the EXACT
formula

  actual target change = 2*theta_i*2^(-K)

for a target word of length K+1>=2. The left side is expectation in
the original prime-cylinder times the actual auxiliary probability.
The right side is proved by the raw-observation identity and disjoint
single-bit translates of the unsigned target orbit. For theta_i>=1/4,
this is at least 2^(-K)/2, the literal half-factor needed in T19.17.
No desired flip cost or target probability is a theorem premise.

The original finite arithmetic raw-dependence and small-pivot exception
counts remain available for source aggregation. The randomized Palm
identity from the previous checkpoint applies on fully private good
sources. A compatible anchored map must be retained on other original
one-small-pivot sources, as the concrete square-anchor scope test shows.
That global hybrid coupling and the final half-factor source summation
have not yet been declared proved. The independent ordinary source
census also remains unformalized.

P1-MATH-0190 records the arbitrary auxiliary-law product semantics,
ordinary quarter-flip selection and exact ACTUAL randomized target-cost
formula. Coverage stays 88 proved and 69 conditional out of 167 numbered
results, with ten incomplete. There are 189 improvements and one
statement-scope correction. No new external theorem, axiom, dependency,
compiler change or source-manuscript edit is introduced. Palomar stays
deferred until completion and statement alignment.
