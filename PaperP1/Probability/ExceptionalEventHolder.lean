module

public import PaperP1.Probability.FiniteHolder
public import PaperP1.Probability.FiniteLaw

/-! # An actual finite eighth-moment bound on the contribution of an exceptional event -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ExceptionalEventHolder

open Finset PaperP1.Algebra PaperP1.Probability

variable {Ω : Type*} [Fintype Ω]

theorem restricted_eighth (P : FiniteProbability Ω) (X : Ω → ℝ) (hX : ∀ ω, 0 ≤ X ω) (B : Ω → Prop) [DecidablePred B] :
    finiteExpectation P.weight (fun ω ↦ if B ω then X ω else 0) ≤
      (finiteExpectation P.weight (fun ω ↦ X ω ^ 8)) ^ (1 / 8 : ℝ) *
        (finiteExpectation P.weight (fun ω ↦ if B ω then 1 else 0)) ^ (7 / 8 : ℝ) := by
  let F : Fin 2 → Ω → ℝ := ![fun ω ↦ X ω ^ 8, fun ω ↦ if B ω then 1 else 0]
  let α : Fin 2 → ℝ := ![1 / 8, 7 / 8]
  have hF : ∀ i ∈ (univ : Finset (Fin 2)), ∀ ω, 0 ≤ F i ω := by
    intro i _hi ω
    fin_cases i
    · exact pow_nonneg (hX ω) _
    · change 0 ≤ if B ω then (1 : ℝ) else 0
      split_ifs <;> norm_num
  have hα : ∀ i ∈ (univ : Finset (Fin 2)), 0 ≤ α i := by
    intro i _hi
    fin_cases i <;> norm_num [α]
  have hsum : (∑ i : Fin 2, α i) = 1 := by norm_num [α, Fin.sum_univ_two]
  have h := FiniteHolder.weighted_geometric_holder P.weight P.weight_nonneg univ F α hF hα hsum
  have hpoint (ω : Ω) : (∏ i : Fin 2, (F i ω) ^ α i) = if B ω then X ω else 0 := by
    have hroot : (X ω ^ 8) ^ (1 / 8 : ℝ) = X ω := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (hX ω)]
      norm_num
    simp only [Fin.prod_univ_two, F, α, Matrix.cons_val_zero, Matrix.cons_val_one, hroot]
    by_cases hb : B ω <;> simp [hb]
  simp_rw [hpoint] at h
  simpa only [Fin.prod_univ_two, F, α, Matrix.cons_val_zero, Matrix.cons_val_one] using h

end PaperP1.ExceptionalEventHolder
