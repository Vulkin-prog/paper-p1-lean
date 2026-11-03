module

public import PaperP1.Combinatorics.SeedComplementMass

/-! # Seed covers with the exact permitted complement population -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RestrictedSeedComplements

open Finset

variable {ι : Type*} [DecidableEq ι]

theorem fiber_bound (F : Finset (Finset ι)) (D : Finset ι) (A : Finset (Finset ι))
    (w : ι → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hF : ∀ I ∈ F, D ⊆ I ∧ I \ D ∈ A) :
    (∑ I ∈ F, ∏ x ∈ I \ D, w x) ≤ ∑ U ∈ A, ∏ x ∈ U, w x := by
  classical
  have hinj : Set.InjOn (fun I : Finset ι ↦ I \ D) (F : Set (Finset ι)) := by
    intro I hI J hJ heq
    calc
      I = D ∪ (I \ D) := (union_sdiff_of_subset (hF I hI).1).symm
      _ = D ∪ (J \ D) := congrArg (fun U : Finset ι ↦ D ∪ U) heq
      _ = J := union_sdiff_of_subset (hF J hJ).1
  have hsub : F.image (fun I ↦ I \ D) ⊆ A := by
    intro U hU
    obtain ⟨I, hI, rfl⟩ := mem_image.mp hU
    exact (hF I hI).2
  calc
    _ = ∑ U ∈ F.image (fun I ↦ I \ D), ∏ x ∈ U, w x := (sum_image hinj).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun U _ _ ↦ prod_nonneg fun x _ ↦ hw x)

theorem cover_bound (F T : Finset (Finset ι)) (A : Finset ι → Finset (Finset ι))
    (w : ι → ℝ) (c f : Finset ι → ℝ) (hw : ∀ x, 0 ≤ w x) (hc : ∀ D ∈ T, 0 ≤ c D)
    (hF : ∀ I ∈ F, ∃ D ∈ T, D ⊆ I ∧ I \ D ∈ A D ∧ f I ≤ c D * ∏ x ∈ I \ D, w x) :
    (∑ I ∈ F, f I) ≤ ∑ D ∈ T, c D * ∑ U ∈ A D, ∏ x ∈ U, w x := by
  classical
  let b : Finset ι → Finset ι → ℝ :=
    fun D I ↦ if D ⊆ I ∧ I \ D ∈ A D then c D * ∏ x ∈ I \ D, w x else 0
  have hb (D : Finset ι) (hD : D ∈ T) (I : Finset ι) : 0 ≤ b D I := by
    dsimp [b]
    split_ifs
    · exact mul_nonneg (hc D hD) (prod_nonneg fun x _ ↦ hw x)
    · exact le_rfl
  have hpoint (I : Finset ι) (hI : I ∈ F) : f I ≤ ∑ D ∈ T, b D I := by
    obtain ⟨D, hD, hDI, hcomp, hbound⟩ := hF I hI
    have h := single_le_sum (fun E hE ↦ hb E hE I) hD
    exact hbound.trans (by simpa only [b, ite_eq_left (And.intro hDI hcomp)] using h)
  calc
    _ ≤ ∑ I ∈ F, ∑ D ∈ T, b D I := sum_le_sum hpoint
    _ = ∑ D ∈ T, ∑ I ∈ F, b D I := sum_comm
    _ ≤ _ := by
      apply sum_le_sum
      intro D hD
      calc
        _ = c D * ∑ I ∈ F.filter (fun I ↦ D ⊆ I ∧ I \ D ∈ A D), ∏ x ∈ I \ D, w x := by
          simp only [b, sum_filter, mul_sum, mul_ite, mul_zero]
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (fiber_bound _ D (A D) w hw (fun _ hI ↦ (mem_filter.mp hI).2)) (hc D hD)

end PaperP1.RestrictedSeedComplements
