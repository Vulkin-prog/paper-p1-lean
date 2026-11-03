module

public import PaperP1.Combinatorics.GraphStarWeights

/-! # Unordered seed covers at all cardinalities retain exact heterogeneous product weights -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AllCardinalitySeedBound

open Finset

variable {ι : Type*} [DecidableEq ι]

def supersets (G D : Finset ι) : Finset (Finset ι) := G.powerset.filter fun U ↦ D ⊆ U

theorem superset_sum (G D : Finset ι) (hDG : D ⊆ G) (w : ι → ℝ) :
    (∑ U ∈ supersets G D, ∏ x ∈ U, w x) = (∏ x ∈ D, w x) * ∏ x ∈ G \ D, (1 + w x) := by
  classical
  have hsplit : (∑ U ∈ supersets G D, ∏ x ∈ U, w x) =
      ∑ A ∈ (G \ D).powerset, ∏ x ∈ D ∪ A, w x := by
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
      have h := congrArg (fun U : Finset ι ↦ U \ D) heq
      simpa only [union_sdiff_cancel_left hAdis, union_sdiff_cancel_left hBdis] using h
    · intro U hU
      obtain ⟨hUG, hDU⟩ := mem_filter.mp hU
      refine ⟨U \ D, mem_powerset.mpr (sdiff_subset_sdiff_left D (mem_powerset.mp hUG)), union_sdiff_of_subset hDU⟩
    · intro A _
      rfl
  rw [hsplit]
  calc
    _ = ∑ A ∈ (G \ D).powerset, (∏ x ∈ D, w x) * ∏ x ∈ A, w x := by
      apply sum_congr rfl
      intro A hA
      exact prod_union (disjoint_left.mpr (fun x hxD hxA ↦
        (mem_sdiff.mp (mem_powerset.mp hA hxA)).2 hxD))
    _ = _ := by rw [← mul_sum, ← prod_one_add]

theorem superset_bound (G D : Finset ι) (hDG : D ⊆ G) (w : ι → ℝ) (hw : ∀ x, 0 ≤ w x) :
    (∑ U ∈ supersets G D, ∏ x ∈ U, w x) ≤ (∏ x ∈ D, w x) * Real.exp (∑ x ∈ G, w x) := by
  rw [superset_sum G D hDG w]
  apply mul_le_mul_of_nonneg_left _ (prod_nonneg fun x _ ↦ hw x)
  exact (Real.prod_one_add_le_exp_sum _ hw).trans (Real.exp_le_exp.mpr
    (sum_le_sum_of_subset_of_nonneg sdiff_subset (fun x _ _ ↦ hw x)))

theorem cover_bound (G : Finset ι) (F T : Finset (Finset ι)) (w : ι → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hT : ∀ D ∈ T, D ⊆ G)
    (hF : ∀ U ∈ F, U ⊆ G ∧ ∃ D ∈ T, D ⊆ U) :
    (∑ U ∈ F, ∏ x ∈ U, w x) ≤ Real.exp (∑ x ∈ G, w x) * ∑ D ∈ T, ∏ x ∈ D, w x := by
  classical
  have hsub : F ⊆ T.biUnion (supersets G) := by
    intro U hU
    obtain ⟨hUG, D, hD, hDU⟩ := hF U hU
    exact mem_biUnion.mpr ⟨D, hD, mem_filter.mpr ⟨mem_powerset.mpr hUG, hDU⟩⟩
  calc
    _ ≤ ∑ U ∈ T.biUnion (supersets G), ∏ x ∈ U, w x :=
      sum_le_sum_of_subset_of_nonneg hsub (fun U _ _ ↦ prod_nonneg fun x _ ↦ hw x)
    _ ≤ ∑ D ∈ T, ∑ U ∈ supersets G D, ∏ x ∈ U, w x :=
      GraphStarWeights.sum_biUnion_le_nonneg T _ _ (fun U ↦ prod_nonneg fun x _ ↦ hw x)
    _ ≤ ∑ D ∈ T, (∏ x ∈ D, w x) * Real.exp (∑ x ∈ G, w x) :=
      sum_le_sum (fun D hD ↦ superset_bound G D (hT D hD) w hw)
    _ = _ := by rw [← sum_mul, mul_comm]

end PaperP1.AllCardinalitySeedBound
