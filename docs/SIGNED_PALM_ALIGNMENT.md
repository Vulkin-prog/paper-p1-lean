# Companion T19.12: the complete signed Palm identity

**Status: proved**, all three conclusions. At this checkpoint coverage is
19 / 167: 9 / 73 main and 10 / 94 companion. Original locator: companion
V1.6, page 76, `p1:limits:signed-palm`,
`companion_sections/limits_appendix.tex:910`; statement hash
`8a29db2bba7dee3608300b620b1d9bb3a6731446e43f2c1407d4fda9b86df720`.

## Exact laws and conditional source convention

`IndicatorDeletion.count_erase_eq_sub` identifies the deleted count with
T_x=Z-J_x, for every sample and every x in the finite ground set G.
`activeLaw` is the actual count law weighted by J_x, before division by p_x.
Its mass is therefore p_x. `ConditionalPalm.conditionalProbability` proves
that dividing the sample weights by their own positive p_x gives a normalized
finite probability space. `activeLaw_eq_conditional` identifies the active
weighted law with p_x times its conditional count law.

If p_x=0, every nonnegative active sample weight is zero, and the entire
active law vanishes. `conditionalPalm` explicitly sums only positive-marginal
sources; `conditionalPalm_eq_palmDifference` proves the exact identity with
the undivided signed expression. No nominal common marginal is substituted.

`MeasureSignedPalm` transfers these facts to arbitrary probability spaces by
observing the entire finite indicator vector. In particular,
`observedConditionalLaw_coeff` proves

`Law(T_x | J_x=1){k} = μ{J_x=1 and T_x=k}/p_x`.

`measureMarginal_eq_event` identifies p_x with the actual event probability,
and `observedConditionalLaw_isProbability` proves normalization and positivity.
`observedPalm_eq_conditional_sum` gives exactly the source's D, omitting
zero-marginal sources. The original sample space need not be finite.

## Raw recurrence and the diagonal error

`sizeWeightedLaw_coeff` identifies K(P)_k=kP_k. The exact size-bias identity
is proved as `sizeWeightedLaw_eq_shift_active`, without independence.
The signed residual is the translate of

`D + B - theta Δ P`, with `B=sum_x p_x(Law(T_x)-Law(Z))`.

`residualLaw_eq_shift` proves this as an equality in the finite signed
convolution ring. Translation by δ₁ is an exact ordinary ℓ¹ isometry
(`FiniteLawShift.l1Norm_shift`), rather than merely a contraction.
The natural coupling from Z to T_x gives

`||B||₁ ≤ 2 sum_x p_x²`.

The proved reverse triangle inequality yields the source's complete bound

`|R(P;m,theta) - ||D-theta Δ P||₁| ≤ 2 sum_x p_x²`.

`observedRecurrenceNorm_eq_tsum` identifies R with the actual sum of the
absolute raw coefficients `kP_k-(m-theta)P_(k-1)-theta P_(k-2)`, using the
actual Bochner mean m. Negative-index coefficients are explicitly zero.
`FiniteLawEmbedding` embeds every finite law injectively as an actual atomic
signed measure. Its singleton masses and ordinary countable ℓ¹ sum agree
exactly with the finite representation. All series here have proved finite
support; no first-moment or exponential-tail input is assumed.

## Coefficients in powers of z-1

`FactorialGeneratingPolynomial.transform` is an actual ring homomorphism
sending δ_k to (1+t)^k. `transform_eq_comp` proves that it is the ordinary
generating polynomial evaluated at 1+t, so its j-th coefficient is precisely
the source coefficient of (z-1)^j.

The subset expansion and the exact reindexing of a source outside a j-subset
give `observed_palm_coefficient`:

`d_j = sum_(A subset G, |A|=j) sum_(x in G\A) (q_(A union {x})-p_x q_A)`.

All q_A are the original Bochner joint moments. The source sum and the
intersection sum are taken with their signs before any norm.

For equal actual marginals p, the derivative of the generating polynomial
is the sum of active deleted generating polynomials. The exact deleted-law
identity gives

`sum_x F_(T_x) = n F_Z - t F'_Z`.

Consequently `uniform_palm_polynomial` gives
`F_D=F'_Z-p(nF_Z-tF'_Z)`. Extracting the coefficient proves

`d_j=(j+1)B_(j+1)-p(n-j)B_j`, where `B_j=E choose(Z,j)`.

Every natural j is included, also zero and orders larger than n. The factor
n-j is a real difference, without an accidental truncated natural subtraction.
`companion_T19_12` combines the norm bound, heterogeneous coefficient formula
and equal-marginal specialization on an arbitrary probability space.

## Validation

The full Lean v4.36.0-rc2 build passed (8,715 jobs), followed by the actual
axiom audit of all 1,592 project theorem/lemma declarations. Only `propext`,
`Classical.choice` and `Quot.sound` occur. Original manuscript identities are
checked separately. No new mathematical finding is identified in this
proposition; all eight existing improvement entries remain separate.
No arithmetic Palm-cost estimate, Stein criterion or approximation rate is
claimed by this identity, and no Palomar registration is made.
