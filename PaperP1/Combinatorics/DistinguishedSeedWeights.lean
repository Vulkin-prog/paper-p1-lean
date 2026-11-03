module

public import PaperP1.Combinatorics.GraphStarWeights

/-! # Distinguished disjoint seeds can be charged to a doubled independent weight on their unions -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DistinguishedSeedWeights

open Finset

variable {ι : Type*} [DecidableEq ι]

theorem union_injective (e : Finset ι) (F : Finset (Finset ι))
    (hF : ∀ A ∈ F, Disjoint e A) : Set.InjOn (fun A ↦ e ∪ A) (F : Set (Finset ι)) := by
  intro A hA B hB heq
  have h := congrArg (fun I : Finset ι ↦ I \ e) heq
  simpa only [union_sdiff_cancel_left (hF A hA), union_sdiff_cancel_left (hF B hB)] using h

theorem mass_bound (P T : Finset (Finset ι)) (F : Finset ι → Finset (Finset ι))
    (w : ι → ℝ) (c : Finset ι → ℝ) (R : ℝ) (hw : ∀ x, 0 ≤ w x) (hR : 0 ≤ R)
    (hc : ∀ e ∈ P, 0 ≤ c e ∧ c e ≤ R * ∏ x ∈ e, w x)
    (hF : ∀ e ∈ P, ∀ A ∈ F e, Disjoint e A ∧ e ∪ A ∈ T) :
    (∑ e ∈ P, c e * ∑ A ∈ F e, ∏ x ∈ A, w x) ≤ R * ∑ I ∈ T, ∏ x ∈ I, 2 * w x := by
  classical
  have hinner (e : Finset ι) (he : e ∈ P) :
      (∑ A ∈ F e, (∏ x ∈ e, w x) * ∏ x ∈ A, w x) ≤
        ∑ I ∈ T.filter (fun I ↦ e ⊆ I), ∏ x ∈ I, w x := by
    calc
      _ = ∑ A ∈ F e, ∏ x ∈ e ∪ A, w x :=
        sum_congr rfl (fun A hA ↦ (prod_union (hF e he A hA).1).symm)
      _ = ∑ I ∈ (F e).image (fun A ↦ e ∪ A), ∏ x ∈ I, w x :=
        (sum_image (f := fun I ↦ ∏ x ∈ I, w x)
          (union_injective e (F e) (fun A hA ↦ (hF e he A hA).1))).symm
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (by
        intro I hI
        obtain ⟨A, hA, rfl⟩ := mem_image.mp hI
        exact mem_filter.mpr ⟨(hF e he A hA).2, subset_union_left⟩)
        (fun I _ _ ↦ prod_nonneg fun x _ ↦ hw x)
  have hcount (I : Finset ι) : ((P.filter (fun e ↦ e ⊆ I)).card : ℝ) ≤ 2 ^ I.card := by
    have hsub : P.filter (fun e ↦ e ⊆ I) ⊆ I.powerset :=
      fun e he ↦ mem_powerset.mpr (mem_filter.mp he).2
    exact_mod_cast (card_le_card hsub).trans_eq (card_powerset I)
  calc
    _ ≤ ∑ e ∈ P, (R * ∏ x ∈ e, w x) * ∑ A ∈ F e, ∏ x ∈ A, w x :=
      sum_le_sum (fun e he ↦ mul_le_mul_of_nonneg_right (hc e he).2
        (sum_nonneg fun A _ ↦ prod_nonneg fun x _ ↦ hw x))
    _ = R * ∑ e ∈ P, ∑ A ∈ F e, (∏ x ∈ e, w x) * ∏ x ∈ A, w x := by
      simp only [← mul_sum, mul_assoc]
    _ ≤ R * ∑ e ∈ P, ∑ I ∈ T.filter (fun I ↦ e ⊆ I), ∏ x ∈ I, w x :=
      mul_le_mul_of_nonneg_left (sum_le_sum hinner) hR
    _ = R * ∑ I ∈ T, ∑ e ∈ P.filter (fun e ↦ e ⊆ I), ∏ x ∈ I, w x := by
      congr 1
      simp only [sum_filter]
      rw [sum_comm]
    _ ≤ R * ∑ I ∈ T, 2 ^ I.card * ∏ x ∈ I, w x := by
      apply mul_le_mul_of_nonneg_left _ hR
      apply sum_le_sum
      intro I _
      rw [sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (hcount I) (prod_nonneg fun x _ ↦ hw x)
    _ = _ := by simp only [prod_mul_distrib, prod_const]

end PaperP1.DistinguishedSeedWeights
