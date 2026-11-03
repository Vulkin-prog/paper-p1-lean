module

public import PaperP1.Combinatorics.GraphStarWeights

/-! # Products containing an edge outside a retained class -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BadPairProductCover

open Finset

variable {ι : Type*} [DecidableEq ι]

theorem bad_cover (E Good : Finset ι) (F : Finset (Finset ι))
    (hF : F ⊆ E.powersetCard 2) :
    F.filter (fun S ↦ ¬S ⊆ Good) ⊆
      (E \ Good).biUnion (fun e ↦ (E.erase e).image (fun f ↦ {e, f})) := by
  classical
  intro S hS
  obtain ⟨hSF, hbad⟩ := mem_filter.mp hS
  obtain ⟨hSE, hcard⟩ := mem_powersetCard.mp (hF hSF)
  obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp hcard
  by_cases ha : a ∈ Good
  · have hb : b ∉ Good := by
      intro hb
      exact hbad (by intro e he; simp only [mem_insert, mem_singleton] at he
                     rcases he with rfl | rfl <;> assumption)
    exact mem_biUnion.mpr ⟨b, mem_sdiff.mpr ⟨hSE (by simp), hb⟩,
      mem_image.mpr ⟨a, mem_erase.mpr ⟨hab, hSE (by simp)⟩, pair_comm _ _⟩⟩
  · exact mem_biUnion.mpr ⟨a, mem_sdiff.mpr ⟨hSE (by simp), ha⟩,
      mem_image.mpr ⟨b, mem_erase.mpr ⟨hab.symm, hSE (by simp)⟩, rfl⟩⟩

theorem bad_bound (E Good : Finset ι) (F : Finset (Finset ι))
    (hF : F ⊆ E.powersetCard 2) (w : ι → ℝ) (hw : ∀ e, 0 ≤ w e) :
    (∑ S ∈ F.filter (fun S ↦ ¬S ⊆ Good), ∏ e ∈ S, w e) ≤
      (∑ e ∈ E, w e) * ∑ e ∈ E \ Good, w e := by
  classical
  calc
    _ ≤ ∑ S ∈ (E \ Good).biUnion (fun e ↦ (E.erase e).image (fun f ↦ {e, f})),
        ∏ e ∈ S, w e := sum_le_sum_of_subset_of_nonneg (bad_cover E Good F hF)
          (fun S _ _ ↦ prod_nonneg fun e _ ↦ hw e)
    _ ≤ ∑ e ∈ E \ Good, ∑ S ∈ (E.erase e).image (fun f ↦ {e, f}), ∏ f ∈ S, w f :=
      GraphStarWeights.sum_biUnion_le_nonneg _ _ _ (fun S ↦ prod_nonneg fun e _ ↦ hw e)
    _ ≤ ∑ e ∈ E \ Good, ∑ f ∈ E.erase e, w e * w f := by
      apply sum_le_sum
      intro e _
      have h := sum_image_le_of_nonneg (s := E.erase e) (g := fun f ↦ {e, f})
        (f := fun S ↦ ∏ f ∈ S, w f) (fun S _ ↦ prod_nonneg fun f _ ↦ hw f)
      exact h.trans_eq (sum_congr rfl fun f hf ↦ prod_pair (mem_erase.mp hf).1.symm)
    _ ≤ ∑ e ∈ E \ Good, ∑ f ∈ E, w e * w f := sum_le_sum fun e _ ↦
      sum_le_sum_of_subset_of_nonneg (erase_subset e E) (fun f _ _ ↦ mul_nonneg (hw e) (hw f))
    _ = (∑ e ∈ E \ Good, w e) * (∑ f ∈ E, w f) := by
      rw [sum_mul]
      exact sum_congr rfl fun e _ ↦ (mul_sum _ _ _).symm
    _ = _ := mul_comm _ _

end PaperP1.BadPairProductCover
