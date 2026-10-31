module

public import PaperP1.Probability.FiniteSignedPalm

/-! # Actual conditional source laws and omission of zero-marginal sources -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ConditionalPalm

open PaperP1.Algebra PaperP1.Probability PaperP1.IndicatorDeletion PaperP1.FiniteSignedPalm Finset

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq ι]

def conditionalProbability (P : FiniteProbability Ω) (J : ι → Ω → Bool) (x : ι)
    (hp : 0 < exactMarginal P J x) : FiniteProbability Ω where
  weight ω := P.weight ω * indicatorValue (J x ω) / exactMarginal P J x
  weight_nonneg ω := div_nonneg
    (mul_nonneg (P.weight_nonneg ω) (by cases J x ω <;> norm_num [indicatorValue])) hp.le
  total_weight := by
    simp_rw [div_eq_mul_inv]
    rw [← sum_mul]
    change exactMarginal P J x * (exactMarginal P J x)⁻¹ = 1
    exact mul_inv_cancel₀ hp.ne'

theorem activeLaw_eq_conditional (G : Finset ι) (P : FiniteProbability Ω)
    (J : ι → Ω → Bool) (x : ι) (hp : 0 < exactMarginal P J x) :
    activeLaw G P.weight J x = scalar (exactMarginal P J x) *
      countLaw (G.erase x) (conditionalProbability P J x hp).weight J := by
  unfold activeLaw countLaw
  rw [mul_sum]
  apply sum_congr rfl
  intro ω _
  rw [← mul_assoc, ← map_mul]
  change scalar (P.weight ω * indicatorValue (J x ω)) * _ =
    scalar (exactMarginal P J x * (P.weight ω * indicatorValue (J x ω) / exactMarginal P J x)) * _
  rw [mul_div_cancel₀ _ hp.ne']

omit [DecidableEq ι] in
theorem conditional_countLaw_coeff (H : Finset ι) (P : FiniteProbability Ω)
    (J : ι → Ω → Bool) (x : ι) (hp : 0 < exactMarginal P J x) (k : ℕ) :
    (countLaw H (conditionalProbability P J x hp).weight J).coeff k =
      finiteExpectation P.weight (fun ω ↦
        if J x ω = true ∧ indicatorCount H J ω = k then 1 else 0) / exactMarginal P J x := by
  classical
  rw [countLaw_coeff]
  unfold finiteExpectation
  simp_rw [div_eq_mul_inv]
  rw [sum_mul]
  apply sum_congr rfl
  intro ω _
  change (if indicatorCount H J ω = k then
      P.weight ω * indicatorValue (J x ω) * (exactMarginal P J x)⁻¹ else 0) = _
  cases J x ω <;> by_cases hk : indicatorCount H J ω = k <;> simp [indicatorValue, hk]

theorem activeLaw_eq_zero_of_marginal_zero (G : Finset ι) (P : FiniteProbability Ω)
    (J : ι → Ω → Bool) (x : ι) (hp : exactMarginal P J x = 0) : activeLaw G P.weight J x = 0 := by
  have hn (ω : Ω) (_hω : ω ∈ univ) : 0 ≤ P.weight ω * indicatorValue (J x ω) := by
    cases J x ω <;> simp [indicatorValue, P.weight_nonneg]
  have hz : ∀ ω, P.weight ω * indicatorValue (J x ω) = 0 := by
    have hsum : (∑ ω, P.weight ω * indicatorValue (J x ω)) = 0 := hp
    intro ω
    exact (sum_eq_zero_iff_of_nonneg hn).mp hsum ω (mem_univ ω)
  unfold activeLaw countLaw
  simp only [hz, map_zero, zero_mul, sum_const_zero]

def conditionalPalm (G : Finset ι) (P : FiniteProbability Ω)
    (J : ι → Ω → Bool) : SignedLaw ℝ :=
  ∑ x ∈ G, if hp : 0 < exactMarginal P J x then scalar (exactMarginal P J x) *
    (countLaw (G.erase x) (conditionalProbability P J x hp).weight J -
      countLaw (G.erase x) P.weight J) else 0

theorem conditionalPalm_eq_palmDifference (G : Finset ι) (P : FiniteProbability Ω)
    (J : ι → Ω → Bool) : conditionalPalm G P J = palmDifference G P J := by
  unfold conditionalPalm palmDifference
  apply sum_congr rfl
  intro x _
  by_cases hp : 0 < exactMarginal P J x
  · rw [dite_eq_left hp, activeLaw_eq_conditional G P J x hp, mul_sub]
  · have hz : exactMarginal P J x = 0 :=
      le_antisymm (le_of_not_gt hp) (exactMarginal_nonneg P J x)
    rw [dite_eq_right hp, activeLaw_eq_zero_of_marginal_zero G P J x hz, hz, map_zero,
      zero_mul, sub_zero]

theorem conditionalPalm_residual_bound (G : Finset ι) (P : FiniteProbability Ω)
    (J : ι → Ω → Bool) (θ : ℝ) :
    |recurrenceNorm G P J θ - l1Norm (conditionalPalm G P J -
      scalar θ * forwardDifference * countLaw G P.weight J)| ≤
        2 * ∑ x ∈ G, (exactMarginal P J x) ^ 2 := by
  rw [conditionalPalm_eq_palmDifference]
  exact signed_palm_residual_bound G P J θ

end PaperP1.ConditionalPalm
