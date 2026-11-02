module

public import PaperP1.Probability.ActivePairCount

/-! # Positive-mass covers preserve finite activation probabilities -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ActiveFamilyCover

open Finset PaperP1.Algebra PaperP1.Probability

variable {Ω ι : Type*} [Fintype Ω]

local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem joint_pos_of_active (P : FiniteProbability Ω) (J : ι → Ω → Bool)
    (e : Finset ι) (ω : Ω) (hw : 0 < P.weight ω) (he : ∀ x ∈ e, J x ω = true) :
    0 < finiteJointMoment P J e := by
  classical
  have hp : (∏ x ∈ e, (indicatorValue (J x ω) : ℝ)) = 1 := by
    rw [indicator_product_eq_indicator, ite_eq_left he]
  have hterm : P.weight ω * (∏ x ∈ e, (indicatorValue (J x ω) : ℝ)) ≤ finiteJointMoment P J e :=
    single_le_sum (fun σ _ ↦ mul_nonneg (P.weight_nonneg σ) (indicator_product_nonneg J e σ)) (mem_univ ω)
  rw [hp, mul_one] at hterm
  exact hw.trans_le hterm

theorem activation_mono (P : FiniteProbability Ω) (J : ι → Ω → Bool)
    (F T : Finset (Finset ι)) (hcover : ∀ e ∈ F, 0 < finiteJointMoment P J e → e ∈ T) :
    finiteExpectation P.weight (fun ω ↦ if 0 < ActivePairCount.value F J ω then 1 else 0) ≤
      finiteExpectation P.weight (fun ω ↦ if 0 < ActivePairCount.value T J ω then 1 else 0) := by
  unfold finiteExpectation
  apply sum_le_sum
  intro ω _
  change P.weight ω * (if 0 < ActivePairCount.value F J ω then 1 else 0) ≤
    P.weight ω * (if 0 < ActivePairCount.value T J ω then 1 else 0)
  by_cases hw : P.weight ω = 0
  · simp only [hw, zero_mul, le_refl]
  have hwpos : 0 < P.weight ω := lt_of_le_of_ne (P.weight_nonneg ω) (Ne.symm hw)
  by_cases hF : 0 < ActivePairCount.value F J ω
  · obtain ⟨e, heF, he⟩ := (ActivePairCount.active_iff_positive F J ω).mpr hF
    have heT := hcover e heF (joint_pos_of_active P J e ω hwpos he)
    have hT := (ActivePairCount.active_iff_positive T J ω).mp ⟨e, heT, he⟩
    simp only [ite_eq_left hF, ite_eq_left hT, le_refl]
  · rw [ite_eq_right hF, mul_zero]
    by_cases hT : 0 < ActivePairCount.value T J ω
    · simp only [ite_eq_left hT, mul_one]
      exact P.weight_nonneg ω
    · simp only [ite_eq_right hT, mul_zero, le_refl]

end PaperP1.ActiveFamilyCover
