module

public import PaperP1.Model.InfiniteJointMoments

/-! # Joint activation decreases when more actual starts are required -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.Model.InfiniteStarts

open Finset PaperP1.Probability PaperP1.Algebra

theorem indicator_product_antitone {Ω ι : Type*} (J : ι → Ω → Bool)
    {A B : Finset ι} (hAB : A ⊆ B) (ω : Ω) :
    (∏ x ∈ B, (indicatorValue (J x ω) : ℝ)) ≤ ∏ x ∈ A, (indicatorValue (J x ω) : ℝ) := by
  classical
  apply prod_le_prod_of_subset_of_le_one₀ hAB
  · intro i _
    cases J i ω <;> norm_num [indicatorValue]
  · intro i _ _
    cases J i ω <;> norm_num [indicatorValue]

theorem finiteJointMoment_antitone {Ω ι : Type*} [Fintype Ω] [LinearOrder ι]
    (P : FiniteProbability Ω) (J : ι → Ω → Bool) {A B : Finset ι} (hAB : A ⊆ B) :
    finiteJointMoment P J B ≤ finiteJointMoment P J A := by
  unfold finiteJointMoment finiteExpectation
  exact sum_le_sum fun ω _ ↦ mul_le_mul_of_nonneg_left
    (indicator_product_antitone J hAB ω) (P.weight_nonneg ω)

theorem infiniteJointMoment_antitone (L : ℕ) {A B : Finset ℕ} (hAB : A ⊆ B) :
    infiniteJointMoment L B ≤ infiniteJointMoment L A := by
  let M := B.sup id + L
  have hB (x : ℕ) (hx : x ∈ B) : x + L ≤ M := by
    have hxle : x ≤ B.sup id := le_sup (f := id) hx
    dsimp [M]
    omega
  rw [infiniteJointMoment_eq_finite M L B hB,
    infiniteJointMoment_eq_finite M L A (fun x hx ↦ hB x (hAB hx))]
  exact finiteJointMoment_antitone _ _ hAB

end PaperP1.Model.InfiniteStarts
