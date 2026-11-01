module

public import PaperP1.Model.LocalBlockBoundaryMass

/-! # A sharper endpoint correction: each nonempty clipped block retains one start -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LocalBlockBoundarySharp

open Finset PaperP1.LocalRelationSets PaperP1.LocalRelationBlocks PaperP1.LocalBlockBoundary
  PaperP1.LocalBlockMass PaperP1.LocalBlockBoundaryMass PaperP1.Arithmetic PaperP1.Model
  PaperP1.Model.InfiniteStarts PaperP1.CountObservables PaperP1.WindowRelationCode

theorem clipped_weight_error (b f e : ℕ) (hb : 1 ≤ b) (hbf : b ≤ f) (he : e ≤ 1)
    (hmiss : e = 0 → b < f) : |((b : ℝ) - 2 * e) - (f - 2)| ≤ (f : ℝ) - 1 := by
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hbfR : (b : ℝ) ≤ f := by exact_mod_cast hbf
  have hecases : e = 0 ∨ e = 1 := by omega
  rcases hecases with rfl | rfl
  · have hgap : (b : ℝ) + 1 ≤ f := by exact_mod_cast hmiss rfl
    norm_num only [Nat.cast_zero, mul_zero, sub_zero]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · norm_num only [Nat.cast_one, mul_one]
    exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem boundaryError_bound_by_length {N L : ℕ} (hN : 2 ≤ N) (hNL : L + 1 ≤ N)
    {S : Finset ℕ} (hS : S ∈ relations N L) :
    |boundaryError N L S| ≤ (((fullBlock L S).card : ℝ) - 1) * (2 ^ L : ℝ)⁻¹ := by
  have hBpos : 1 ≤ (block N L S).card := card_pos.mpr (block_nonempty hS)
  have hsub := block_subset_full hN hNL hS
  have he : endpointCount N S ≤ 1 := by unfold endpointCount; split_ifs <;> omega
  have hmiss : endpointCount N S = 0 → (block N L S).card < (fullBlock L S).card := by
    intro he0
    have hend : first S + 1 ∉ dyadicBlock N := by
      intro h
      simp only [endpointCount, ite_eq_left h] at he0
      omega
    have hnotB : first S + 1 ∉ block N L S := by
      simpa only [endpoint_mem_block_iff hN hS] using hend
    have hne : block N L S ≠ fullBlock L S := by
      intro heq
      exact hnotB (heq ▸ endpoint_mem_full hN hNL hS)
    exact card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
  have hcore := clipped_weight_error (block N L S).card (fullBlock L S).card (endpointCount N S)
    hBpos (card_le_card hsub) he hmiss
  calc
    _ = |(((block N L S).card : ℝ) - 2 * (endpointCount N S : ℝ)) -
        ((fullBlock L S).card - 2)| * (2 ^ L : ℝ)⁻¹ := by
      rw [boundaryError, abs_mul, abs_of_nonneg (by positivity)]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcore (by positivity)

theorem sum_boundaryError_bound_by_lengths {N L : ℕ} (hN : 2 ≤ N) (hNL : L + 1 ≤ N) :
    |∑ S ∈ relations N L, boundaryError N L S| ≤
      (2 ^ L : ℝ)⁻¹ * ∑ S ∈ truncated N L, (((fullBlock L S).card : ℝ) - 1) := by
  classical
  have hrestrict : (∑ S ∈ truncated N L, boundaryError N L S) = ∑ S ∈ relations N L, boundaryError N L S := by
    apply sum_subset (filter_subset _ _)
    intro S hS hnot
    have hfull : fullBlock L S ⊆ dyadicBlock N := by
      by_contra h
      exact hnot (mem_filter.mpr ⟨hS, h⟩)
    exact boundaryError_zero hN hNL hS hfull
  calc
    _ = |∑ S ∈ truncated N L, boundaryError N L S| := by rw [hrestrict]
    _ ≤ ∑ S ∈ truncated N L, |boundaryError N L S| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ S ∈ truncated N L, (((fullBlock L S).card : ℝ) - 1) * (2 ^ L : ℝ)⁻¹ :=
      sum_le_sum fun S hS ↦ boundaryError_bound_by_length hN hNL (mem_filter.mp hS).1
    _ = _ := by rw [← sum_mul]; ring

theorem sum_boundaryError_bound_sharp {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (hNL : L + 1 ≤ N)
    (hrank : ∀ x ∈ dyadicBlock N, Module.finrank F₂ (windowRelationCode (x - 1) (L + 1)) ≤ 1) :
    |∑ S ∈ relations N L, boundaryError N L S| ≤ 2 * ((L : ℝ) - 1) * (2 ^ L : ℝ)⁻¹ := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hcard : ((truncated N L).card : ℝ) ≤ 2 := by exact_mod_cast truncated_card_le_two hN hNL hrank
  calc
    _ ≤ (2 ^ L : ℝ)⁻¹ * ∑ S ∈ truncated N L, (((fullBlock L S).card : ℝ) - 1) :=
      sum_boundaryError_bound_by_lengths hN hNL
    _ ≤ (2 ^ L : ℝ)⁻¹ * ∑ _S ∈ truncated N L, ((L : ℝ) - 1) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply sum_le_sum
      intro S hS
      have hF : ((fullBlock L S).card : ℝ) ≤ L := by
        exact_mod_cast fullBlock_card_le_length hN hNL (mem_filter.mp hS).1
      linarith
    _ = ((truncated N L).card : ℝ) * (((L : ℝ) - 1) * (2 ^ L : ℝ)⁻¹) := by simp; ring
    _ ≤ 2 * (((L : ℝ) - 1) * (2 ^ L : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_right hcard (mul_nonneg (by linarith) (by positivity))
    _ = _ := by ring

theorem mean_full_block_error_sharp {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (hNL : L + 1 ≤ N)
    (hrank : ∀ x ∈ dyadicBlock N, Module.finrank F₂ (windowRelationCode (x - 1) (L + 1)) ≤ 1) :
    |countMoment (dyadicBlock N) L 1 - N * (2 ^ L : ℝ)⁻¹ -
      (2 ^ L : ℝ)⁻¹ * ∑ S ∈ relations N L, ((L : ℝ) - (last S - first S : ℕ) - 1)| ≤
        2 * ((L : ℝ) - 1) * (2 ^ L : ℝ)⁻¹ := by
  have heq : countMoment (dyadicBlock N) L 1 - N * (2 ^ L : ℝ)⁻¹ -
      (2 ^ L : ℝ)⁻¹ * ∑ S ∈ relations N L, ((L : ℝ) - (last S - first S : ℕ) - 1) =
      ∑ S ∈ relations N L, boundaryError N L S := by
    rw [mean_discrepancy hN hL hrank, mul_sum, mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro S hS
    rw [boundaryError, fullBlock_card_real hN hNL hS]
    ring
  rw [heq]
  exact sum_boundaryError_bound_sharp hN hL hNL hrank

end PaperP1.LocalBlockBoundarySharp
