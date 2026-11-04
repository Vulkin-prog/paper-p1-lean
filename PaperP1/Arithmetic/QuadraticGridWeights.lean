module

public import PaperP1.Arithmetic.QuadraticIntervalGrid

/-! # Literal transfer of nonnegative interval weights through the quadratic grid -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.QuadraticGridWeights

open Finset PaperP1.QuadraticIntervalGrid

theorem image_subset (M : ℕ) (hM : 32 ≤ M) (I : Finset ℕ)
    (hlow : ∀ k ∈ I, M ≤ 4 * k) (hupper : ∀ k ∈ I, k ≤ 2 * M) :
    I.image (grid M) ⊆ Icc 1 (4 * M) := by
  intro q hq
  obtain ⟨k, hk, rfl⟩ := mem_image.mp hq
  have hlo := grid_lower M k hM (hlow k hk)
  have hhi := grid_upper M k (by omega) (hupper k hk)
  exact mem_Icc.mpr ⟨by omega, hhi⟩

theorem weighted_sum_bound (M : ℕ) (hM : 0 < M) (I : Finset ℕ)
    (hlow : ∀ k ∈ I, M ≤ 4 * k) (w : ℕ → ℝ) (hw : ∀ q ∈ I.image (grid M), 0 ≤ w q) :
    (∑ k ∈ I, w (grid M k)) ≤ 2 * ∑ q ∈ I.image (grid M), w q := by
  calc
    _ = ∑ q ∈ I.image (grid M), ((I.filter (fun k ↦ grid M k = q)).card : ℝ) * w q := by
      simpa only [nsmul_eq_mul] using Finset.sum_comp (s := I) w (grid M)
    _ ≤ ∑ q ∈ I.image (grid M), 2 * w q := by
      apply sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast fibre_card M hM I hlow q) (hw q hq)
    _ = _ := (Finset.mul_sum ..).symm

end PaperP1.QuadraticGridWeights
