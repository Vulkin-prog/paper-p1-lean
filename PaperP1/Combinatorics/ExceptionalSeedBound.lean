module

public import PaperP1.Combinatorics.AllCardinalitySeedBound

/-! # An unordered exceptional-seed argument closes every cardinality using two finite exponential products -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ExceptionalSeedBound

open Finset

attribute [local instance] Classical.propDecidable

variable {ι : Type*} [DecidableEq ι]

def seeds (G : Finset ι) (bad : Finset ι → ι → Prop) : Finset (Finset ι) := by
  classical
  exact G.powerset.biUnion fun A ↦ ((G \ A).filter (bad A)).image (fun x ↦ insert x A)

theorem seed_mass (G : Finset ι) (bad : Finset ι → ι → Prop) (w : ι → ℝ) (hw : ∀ x, 0 ≤ w x) :
    (∑ D ∈ seeds G bad, ∏ x ∈ D, w x) ≤
      ∑ A ∈ G.powerset, (∏ x ∈ A, w x) * ∑ x ∈ G.filter (bad A), w x := by
  classical
  calc
    _ ≤ ∑ A ∈ G.powerset, ∑ D ∈ ((G \ A).filter (bad A)).image (fun x ↦ insert x A), ∏ x ∈ D, w x :=
      GraphStarWeights.sum_biUnion_le_nonneg _ _ _ (fun D ↦ prod_nonneg fun x _ ↦ hw x)
    _ ≤ ∑ A ∈ G.powerset, ∑ x ∈ (G \ A).filter (bad A), ∏ y ∈ insert x A, w y :=
      sum_le_sum (fun _ _ ↦ sum_image_le_of_nonneg (fun D _ ↦ prod_nonneg fun y _ ↦ hw y))
    _ = ∑ A ∈ G.powerset, (∏ y ∈ A, w y) * ∑ x ∈ (G \ A).filter (bad A), w x := by
      apply sum_congr rfl
      intro A _
      rw [mul_sum]
      apply sum_congr rfl
      intro x hx
      rw [prod_insert (mem_sdiff.mp (mem_filter.mp hx).1).2, mul_comm]
    _ ≤ _ := by
      apply sum_le_sum
      intro A _
      apply mul_le_mul_of_nonneg_left _ (prod_nonneg fun x _ ↦ hw x)
      exact sum_le_sum_of_subset_of_nonneg (fun x hx ↦ mem_filter.mpr
        ⟨(mem_sdiff.mp (mem_filter.mp hx).1).1, (mem_filter.mp hx).2⟩) (fun x _ _ ↦ hw x)

theorem cover_mass (G : Finset ι) (F : Finset (Finset ι)) (bad : Finset ι → ι → Prop)
    (w a : ι → ℝ) (hw : ∀ x, 0 ≤ w x) (ha : ∀ x, 1 ≤ a x) (D : ℝ) (hD : 0 ≤ D)
    (hrow : ∀ A ⊆ G, (∑ x ∈ G.filter (bad A), w x) ≤ D * ∏ x ∈ A, a x)
    (hF : ∀ U ∈ F, U ⊆ G ∧ ∃ A ⊆ U, ∃ x ∈ U, x ∉ A ∧ bad A x) :
    (∑ U ∈ F, ∏ x ∈ U, w x) ≤ D * Real.exp ((∑ x ∈ G, w x) + ∑ x ∈ G, w x * a x) := by
  classical
  have hT : ∀ T ∈ seeds G bad, T ⊆ G := by
    intro T hT
    obtain ⟨A, hA, hT⟩ := mem_biUnion.mp hT
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hT
    exact insert_subset_iff.mpr ⟨(mem_sdiff.mp (mem_filter.mp hx).1).1, mem_powerset.mp hA⟩
  have hcover : ∀ U ∈ F, U ⊆ G ∧ ∃ T ∈ seeds G bad, T ⊆ U := by
    intro U hU
    obtain ⟨hUG, A, hAU, x, hxU, hxnot, hbad⟩ := hF U hU
    refine ⟨hUG, insert x A, ?_, insert_subset_iff.mpr ⟨hxU, hAU⟩⟩
    exact mem_biUnion.mpr ⟨A, mem_powerset.mpr (hAU.trans hUG), mem_image.mpr
      ⟨x, mem_filter.mpr ⟨mem_sdiff.mpr ⟨hUG hxU, hxnot⟩, hbad⟩, rfl⟩⟩
  have hseeds : (∑ T ∈ seeds G bad, ∏ x ∈ T, w x) ≤ D * Real.exp (∑ x ∈ G, w x * a x) := by
    calc
      _ ≤ ∑ A ∈ G.powerset, (∏ x ∈ A, w x) * ∑ x ∈ G.filter (bad A), w x := seed_mass G bad w hw
      _ ≤ ∑ A ∈ G.powerset, (∏ x ∈ A, w x) * (D * ∏ x ∈ A, a x) :=
        sum_le_sum (fun A hA ↦ mul_le_mul_of_nonneg_left (hrow A (mem_powerset.mp hA))
          (prod_nonneg fun x _ ↦ hw x))
      _ = D * ∑ A ∈ G.powerset, ∏ x ∈ A, w x * a x := by
        rw [mul_sum]
        apply sum_congr rfl
        intro A _
        rw [prod_mul_distrib]
        ring
      _ = D * ∏ x ∈ G, (1 + w x * a x) := by rw [← prod_one_add]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.prod_one_add_le_exp_sum _
        (fun x ↦ mul_nonneg (hw x) ((by norm_num : (0 : ℝ) ≤ 1).trans (ha x)))) hD
  calc
    _ ≤ Real.exp (∑ x ∈ G, w x) * ∑ T ∈ seeds G bad, ∏ x ∈ T, w x :=
      AllCardinalitySeedBound.cover_bound G F (seeds G bad) w hw hT hcover
    _ ≤ Real.exp (∑ x ∈ G, w x) * (D * Real.exp (∑ x ∈ G, w x * a x)) :=
      mul_le_mul_of_nonneg_left hseeds (Real.exp_nonneg _)
    _ = _ := by rw [Real.exp_add]; ring

theorem constant_bound (G : Finset ι) (F : Finset (Finset ι)) (bad : Finset ι → ι → Prop)
    (w a : ι → ℝ) (hw : ∀ x, 0 ≤ w x) (ha : ∀ x, 1 ≤ a x) (D K : ℝ) (hD : 0 ≤ D)
    (hK : (∑ x ∈ G, w x * a x) ≤ K)
    (hrow : ∀ A ⊆ G, (∑ x ∈ G.filter (bad A), w x) ≤ D * ∏ x ∈ A, a x)
    (hF : ∀ U ∈ F, U ⊆ G ∧ ∃ A ⊆ U, ∃ x ∈ U, x ∉ A ∧ bad A x) :
    (∑ U ∈ F, ∏ x ∈ U, w x) ≤ D * Real.exp (2 * K) := by
  have hmean : (∑ x ∈ G, w x) ≤ K := by
    apply le_trans _ hK
    apply sum_le_sum
    intro x _
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (ha x) (hw x)
  exact (cover_mass G F bad w a hw ha D hD hrow hF).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hmean, hK])) hD)

end PaperP1.ExceptionalSeedBound
