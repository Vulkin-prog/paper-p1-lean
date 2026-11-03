module

public import PaperP1.Combinatorics.SeedComplementMass

/-! # Sum every contained seed with its own activity and the exact independently weighted complement -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SeedComplementSum

open Finset PaperP1.AllCardinalitySeedBound

variable {ι : Type*} [DecidableEq ι]

theorem finite_bound (G : Finset ι) (F T : Finset (Finset ι)) (w : ι → ℝ) (c : Finset ι → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hc : ∀ D ∈ T, 0 ≤ c D)
    (hF : ∀ I ∈ F, I ⊆ G) (hT : ∀ D ∈ T, D ⊆ G) :
    (∑ I ∈ F, ∑ D ∈ T, if D ⊆ I then c D * ∏ x ∈ I \ D, w x else 0) ≤
      Real.exp (∑ x ∈ G, w x) * ∑ D ∈ T, c D := by
  classical
  rw [sum_comm]
  calc
    _ ≤ ∑ D ∈ T, c D * Real.exp (∑ x ∈ G, w x) := by
      apply sum_le_sum
      intro D hD
      have hsub : F.filter (fun I ↦ D ⊆ I) ⊆ supersets G D := by
        intro I hI
        obtain ⟨hIF, hDI⟩ := mem_filter.mp hI
        exact mem_filter.mpr ⟨mem_powerset.mpr (hF I hIF), hDI⟩
      calc
        _ = c D * ∑ I ∈ F.filter (fun I ↦ D ⊆ I), ∏ x ∈ I \ D, w x := by
          simp only [sum_filter, mul_sum, mul_ite, mul_zero]
        _ ≤ c D * ∑ I ∈ supersets G D, ∏ x ∈ I \ D, w x :=
          mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg hsub
            (fun I _ _ ↦ prod_nonneg fun x _ ↦ hw x)) (hc D hD)
        _ ≤ _ := mul_le_mul_of_nonneg_left (SeedComplementMass.complement_bound G D (hT D hD) w hw) (hc D hD)
    _ = _ := by rw [← sum_mul, mul_comm]

end PaperP1.SeedComplementSum
