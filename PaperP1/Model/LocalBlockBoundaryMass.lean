module

public import PaperP1.Model.LocalBlockMass
public import PaperP1.Arithmetic.LocalBlockBoundary

/-! # The full-block contribution and the exact endpoint correction bounded by 2Lp -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LocalBlockBoundaryMass

open Finset PaperP1.LocalRelationSets PaperP1.LocalRelationBlocks PaperP1.LocalBlockBoundary
  PaperP1.LocalBlockMass PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.CountObservables PaperP1.WindowRelationCode

def boundaryError (N L : ℕ) (S : Finset ℕ) : ℝ :=
  (2 ^ L : ℝ)⁻¹ * (((block N L S).card - 2 * (endpointCount N S : ℝ)) -
    ((fullBlock L S).card - 2))

theorem fullBlock_card_real {N L : ℕ} (hN : 2 ≤ N) (hNL : L + 1 ≤ N)
    {S : Finset ℕ} (hS : S ∈ relations N L) :
    ((fullBlock L S).card : ℝ) = (L : ℝ) - (last S - first S : ℕ) + 1 := by
  have hab := first_le_last ((mem_relations N L S).mp hS).1.1
  have hbL := last_ge_length hNL hS
  obtain ⟨x, hx⟩ := fullBlock_nonempty hN hNL hS
  have hb := mem_Icc.mp hx
  have hdiam : last S - first S ≤ L := by omega
  rw [fullBlock_card hN hNL hS, Nat.cast_add, Nat.cast_one, Nat.cast_sub hdiam]

theorem full_block_contribution {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (hNL : L + 1 ≤ N)
    (hrank : ∀ x ∈ dyadicBlock N, Module.finrank F₂ (windowRelationCode (x - 1) (L + 1)) ≤ 1)
    {S : Finset ℕ} (hS : S ∈ relations N L) (hfull : fullBlock L S ⊆ dyadicBlock N) :
    (∑ x ∈ block N L S, (infiniteMarginal x L - (2 ^ L : ℝ)⁻¹)) =
      (2 ^ L : ℝ)⁻¹ * ((L : ℝ) - (last S - first S : ℕ) - 1) := by
  have hend : first S + 1 ∈ dyadicBlock N := hfull (endpoint_mem_full hN hNL hS)
  rw [block_signed_discrepancy hN hL hrank hS, block_eq_full_of_subset hN hNL hS hfull,
    endpointCount, ite_eq_left hend, Nat.cast_one, fullBlock_card_real hN hNL hS]
  ring

theorem boundaryError_zero {N L : ℕ} (hN : 2 ≤ N) (hNL : L + 1 ≤ N)
    {S : Finset ℕ} (hS : S ∈ relations N L) (hfull : fullBlock L S ⊆ dyadicBlock N) :
    boundaryError N L S = 0 := by
  have hend : first S + 1 ∈ dyadicBlock N := hfull (endpoint_mem_full hN hNL hS)
  rw [boundaryError, block_eq_full_of_subset hN hNL hS hfull, endpointCount, ite_eq_left hend, Nat.cast_one]
  ring

theorem boundaryError_bound {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (hNL : L + 1 ≤ N)
    {S : Finset ℕ} (hS : S ∈ relations N L) : |boundaryError N L S| ≤ L * (2 ^ L : ℝ)⁻¹ := by
  classical
  have hsub := block_subset_full hN hNL hS
  have hB : ((block N L S).card : ℝ) ≤ (fullBlock L S).card := by exact_mod_cast card_le_card hsub
  have hF : ((fullBlock L S).card : ℝ) ≤ L := by exact_mod_cast fullBlock_card_le_length hN hNL hS
  have hB0 : (0 : ℝ) ≤ (block N L S).card := Nat.cast_nonneg _
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hcore : |(((block N L S).card : ℝ) - 2 * (endpointCount N S : ℝ)) -
      ((fullBlock L S).card - 2)| ≤ L := by
    by_cases hend : first S + 1 ∈ dyadicBlock N
    · simp only [endpointCount, ite_eq_left hend, Nat.cast_one]
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    · have hnotB : first S + 1 ∉ block N L S := by
        simpa only [endpoint_mem_block_iff hN hS] using hend
      have hne : block N L S ≠ fullBlock L S := by
        intro heq
        exact hnotB (heq ▸ endpoint_mem_full hN hNL hS)
      have hlt := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
      have hgap : ((block N L S).card : ℝ) + 1 ≤ (fullBlock L S).card := by exact_mod_cast hlt
      simp only [endpointCount, ite_eq_right hend, Nat.cast_zero, mul_zero, sub_zero]
      exact abs_le.mpr ⟨by linarith, by linarith⟩
  calc
    _ = (2 ^ L : ℝ)⁻¹ * |(((block N L S).card : ℝ) - 2 * (endpointCount N S : ℝ)) -
        ((fullBlock L S).card - 2)| := by rw [boundaryError, abs_mul, abs_of_nonneg (by positivity)]
    _ ≤ (2 ^ L : ℝ)⁻¹ * L := mul_le_mul_of_nonneg_left hcore (by positivity)
    _ = _ := by ring

theorem sum_boundaryError_bound {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (hNL : L + 1 ≤ N)
    (hrank : ∀ x ∈ dyadicBlock N, Module.finrank F₂ (windowRelationCode (x - 1) (L + 1)) ≤ 1) :
    |∑ S ∈ relations N L, boundaryError N L S| ≤ 2 * L * (2 ^ L : ℝ)⁻¹ := by
  classical
  have hrestrict : (∑ S ∈ truncated N L, boundaryError N L S) = ∑ S ∈ relations N L, boundaryError N L S := by
    apply sum_subset (filter_subset _ _)
    intro S hS hnot
    have hfull : fullBlock L S ⊆ dyadicBlock N := by
      by_contra h
      exact hnot (mem_filter.mpr ⟨hS, h⟩)
    exact boundaryError_zero hN hNL hS hfull
  have hcard : ((truncated N L).card : ℝ) ≤ 2 := by exact_mod_cast truncated_card_le_two hN hNL hrank
  calc
    _ = |∑ S ∈ truncated N L, boundaryError N L S| := by rw [hrestrict]
    _ ≤ ∑ S ∈ truncated N L, |boundaryError N L S| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _S ∈ truncated N L, (L : ℝ) * (2 ^ L : ℝ)⁻¹ :=
      sum_le_sum fun S hS ↦ boundaryError_bound hN hL hNL (mem_filter.mp hS).1
    _ = ((truncated N L).card : ℝ) * ((L : ℝ) * (2 ^ L : ℝ)⁻¹) := by simp
    _ ≤ 2 * ((L : ℝ) * (2 ^ L : ℝ)⁻¹) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

theorem mean_full_block_error {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (hNL : L + 1 ≤ N)
    (hrank : ∀ x ∈ dyadicBlock N, Module.finrank F₂ (windowRelationCode (x - 1) (L + 1)) ≤ 1) :
    |countMoment (dyadicBlock N) L 1 - N * (2 ^ L : ℝ)⁻¹ -
      (2 ^ L : ℝ)⁻¹ * ∑ S ∈ relations N L, ((L : ℝ) - (last S - first S : ℕ) - 1)| ≤
        2 * L * (2 ^ L : ℝ)⁻¹ := by
  have heq : countMoment (dyadicBlock N) L 1 - N * (2 ^ L : ℝ)⁻¹ -
      (2 ^ L : ℝ)⁻¹ * ∑ S ∈ relations N L, ((L : ℝ) - (last S - first S : ℕ) - 1) =
      ∑ S ∈ relations N L, boundaryError N L S := by
    rw [mean_discrepancy hN hL hrank, mul_sum, mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro S hS
    rw [boundaryError, fullBlock_card_real hN hNL hS]
    ring
  rw [heq]
  exact sum_boundaryError_bound hN hL hNL hrank

end PaperP1.LocalBlockBoundaryMass
