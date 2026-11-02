module

public import PaperP1.Model.CompatibleActivitySplit
public import PaperP1.Combinatorics.GraphStarWeights

/-! # A positive cover of nonzero actual coefficients bounds total centered activity -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ActivityFamilyCover

open Finset PaperP1.Model.InfiniteStarts

local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem finite_cover {ι : Type*} (L : ℕ) (F : Finset (Finset ℕ)) (S : Finset ι)
    (A : ι → Finset (Finset ℕ))
    (hcover : ∀ e ∈ F, infiniteCenteredCoefficient L e ≠ 0 → ∃ i ∈ S, e ∈ A i) :
    CompatibleActivitySplit.absolute L F ≤ ∑ i ∈ S, CompatibleActivitySplit.absolute L (A i) := by
  let T := F.filter fun e ↦ infiniteCenteredCoefficient L e ≠ 0
  have heq : CompatibleActivitySplit.absolute L F = ∑ e ∈ T, |infiniteCenteredCoefficient L e| := by
    symm
    apply sum_subset (filter_subset _ _)
    intro e he hnot
    have hz : infiniteCenteredCoefficient L e = 0 := by
      by_contra hn
      exact hnot (mem_filter.mpr ⟨he, hn⟩)
    rw [hz, abs_zero]
  rw [heq]
  calc
    _ ≤ ∑ e ∈ S.biUnion A, |infiniteCenteredCoefficient L e| :=
      sum_le_sum_of_subset_of_nonneg (fun e he ↦ mem_biUnion.mpr
        (hcover e (mem_filter.mp he).1 (mem_filter.mp he).2)) (fun _ _ _ ↦ abs_nonneg _)
    _ ≤ _ := GraphStarWeights.sum_biUnion_le_nonneg S A
      (fun e ↦ |infiniteCenteredCoefficient L e|) (fun _ ↦ abs_nonneg _)

theorem two_families (L : ℕ) (F U Z : Finset (Finset ℕ))
    (hcover : ∀ e ∈ F, infiniteCenteredCoefficient L e ≠ 0 → e ∈ U ∪ Z) :
    CompatibleActivitySplit.absolute L F ≤ CompatibleActivitySplit.absolute L U + CompatibleActivitySplit.absolute L Z := by
  let A : Bool → Finset (Finset ℕ) := fun b ↦ if b then Z else U
  have hb : ∀ e ∈ F, infiniteCenteredCoefficient L e ≠ 0 → ∃ b ∈ (univ : Finset Bool), e ∈ A b := by
    intro e he hn
    rcases mem_union.mp (hcover e he hn) with h | h
    · exact ⟨false, mem_univ _, h⟩
    · exact ⟨true, mem_univ _, h⟩
  have h := finite_cover L F univ A hb
  simpa only [A, Fintype.sum_bool, Bool.false_eq_true, ite_false, ite_true, add_comm] using h

end PaperP1.ActivityFamilyCover
