module

public import PaperP1.Combinatorics.AllCardinalitySeedBound

/-! # Arbitrary nonnegative seed activities with independently weighted free complements -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SeedComplementMass

open Finset PaperP1.AllCardinalitySeedBound

variable {ι : Type*} [DecidableEq ι]

theorem complement_sum (G D : Finset ι) (hDG : D ⊆ G) (w : ι → ℝ) :
    (∑ I ∈ supersets G D, ∏ x ∈ I \ D, w x) = ∏ x ∈ G \ D, (1 + w x) := by
  classical
  rw [prod_one_add]
  symm
  apply sum_bij (fun A _ ↦ D ∪ A)
  · intro A hA
    have hAG := mem_powerset.mp hA
    exact mem_filter.mpr ⟨mem_powerset.mpr (union_subset hDG (hAG.trans sdiff_subset)), subset_union_left⟩
  · intro A hA B hB heq
    have hAdis : Disjoint D A := disjoint_left.mpr
      (fun x hxD hxA ↦ (mem_sdiff.mp (mem_powerset.mp hA hxA)).2 hxD)
    have hBdis : Disjoint D B := disjoint_left.mpr
      (fun x hxD hxB ↦ (mem_sdiff.mp (mem_powerset.mp hB hxB)).2 hxD)
    have h := congrArg (fun I : Finset ι ↦ I \ D) heq
    simpa only [union_sdiff_cancel_left hAdis, union_sdiff_cancel_left hBdis] using h
  · intro I hI
    obtain ⟨hIG, hDI⟩ := mem_filter.mp hI
    exact ⟨I \ D, mem_powerset.mpr (sdiff_subset_sdiff_left D (mem_powerset.mp hIG)),
      union_sdiff_of_subset hDI⟩
  · intro A hA
    have hAdis : Disjoint D A := disjoint_left.mpr
      (fun x hxD hxA ↦ (mem_sdiff.mp (mem_powerset.mp hA hxA)).2 hxD)
    rw [union_sdiff_cancel_left hAdis]

theorem complement_bound (G D : Finset ι) (hDG : D ⊆ G) (w : ι → ℝ) (hw : ∀ x, 0 ≤ w x) :
    (∑ I ∈ supersets G D, ∏ x ∈ I \ D, w x) ≤ Real.exp (∑ x ∈ G, w x) := by
  rw [complement_sum G D hDG w]
  exact (Real.prod_one_add_le_exp_sum _ hw).trans (Real.exp_le_exp.mpr
    (sum_le_sum_of_subset_of_nonneg sdiff_subset (fun x _ _ ↦ hw x)))

theorem cover_bound (G : Finset ι) (F T : Finset (Finset ι))
    (w : ι → ℝ) (c f : Finset ι → ℝ) (hw : ∀ x, 0 ≤ w x) (hc : ∀ D ∈ T, 0 ≤ c D)
    (hT : ∀ D ∈ T, D ⊆ G)
    (hF : ∀ I ∈ F, I ⊆ G ∧ ∃ D ∈ T, D ⊆ I ∧ f I ≤ c D * ∏ x ∈ I \ D, w x) :
    (∑ I ∈ F, f I) ≤ Real.exp (∑ x ∈ G, w x) * ∑ D ∈ T, c D := by
  classical
  let b : Finset ι → Finset ι → ℝ := fun D I ↦ if D ⊆ I then c D * ∏ x ∈ I \ D, w x else 0
  have hb (D : Finset ι) (hD : D ∈ T) (I : Finset ι) : 0 ≤ b D I := by
    dsimp [b]
    split_ifs
    · exact mul_nonneg (hc D hD) (prod_nonneg fun x _ ↦ hw x)
    · exact le_rfl
  have hpoint (I : Finset ι) (hI : I ∈ F) : f I ≤ ∑ D ∈ T, b D I := by
    obtain ⟨_hIG, D, hD, hDI, hbound⟩ := hF I hI
    have h := single_le_sum (fun E hE ↦ hb E hE I) hD
    exact hbound.trans (by simpa only [b, ite_eq_left hDI] using h)
  calc
    _ ≤ ∑ I ∈ F, ∑ D ∈ T, b D I := sum_le_sum hpoint
    _ = ∑ D ∈ T, ∑ I ∈ F, b D I := sum_comm
    _ ≤ ∑ D ∈ T, c D * Real.exp (∑ x ∈ G, w x) := by
      apply sum_le_sum
      intro D hD
      have hsub : F.filter (fun I ↦ D ⊆ I) ⊆ supersets G D := by
        intro I hI
        obtain ⟨hIF, hDI⟩ := mem_filter.mp hI
        exact mem_filter.mpr ⟨mem_powerset.mpr (hF I hIF).1, hDI⟩
      calc
        _ = c D * ∑ I ∈ F.filter (fun I ↦ D ⊆ I), ∏ x ∈ I \ D, w x := by
          simp only [b, sum_filter, mul_sum, mul_ite, mul_zero]
        _ ≤ c D * ∑ I ∈ supersets G D, ∏ x ∈ I \ D, w x :=
          mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg hsub
            (fun I _ _ ↦ prod_nonneg fun x _ ↦ hw x)) (hc D hD)
        _ ≤ _ := mul_le_mul_of_nonneg_left (complement_bound G D (hT D hD) w hw) (hc D hD)
    _ = _ := by rw [← sum_mul, mul_comm]

end PaperP1.SeedComplementMass
