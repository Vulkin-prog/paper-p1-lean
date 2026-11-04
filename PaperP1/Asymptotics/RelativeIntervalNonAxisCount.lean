module

public import PaperP1.Arithmetic.IntervalProductDivisorCount

/-! # Actual non-axis source intervals have a uniform divisor-controlled tail count -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RelativeIntervalNonAxisCount

open Finset PaperP1.RelativeIntervalLattice PaperP1.RelativeIntervalShortVectors
open PaperP1.DeterminantRelativeIntervals PaperP1.BinaryLatticeMinimum PaperP1.BinaryEuclideanReduction
open PaperP1.BinaryLatticeCoordinateBounds

theorem uniform_nonaxis_intervals (κ : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ M : ℕ, 1 ≤ M → M ≤ N →
      ∀ D E L : ℝ, 0 < D → 0 < E → 0 < L →
      ∀ I : Finset ℕ, I ⊆ intervalIndices M → ∀ z : ℕ → Fin 2 → ℤ,
      (∀ k ∈ I, z k 0 ≠ 0 ∧ z k 1 ≠ 0 ∧ (z k 1).natAbs ≤ N ^ κ) →
      (∀ k ∈ I, L ≤ sideLength 2 (squareNorm
        (realImage (transform D E M (intervalCenter M D E k)) (z k)))) →
      (I.card : ℝ) ≤ 432 * (N : ℝ) ^ ε * (D * E) / L ^ 2 := by
  obtain ⟨N₀, hcount⟩ := IntervalProductDivisorCount.uniform_interval_count κ ε hε
  refine ⟨N₀, ?_⟩
  intro N hN M hM hMN D E L hD hE hL I hI z hnonzero hside
  have hsides (k : ℕ) (hk : k ∈ I) :
      |(z k 0 : ℝ)| ≤ 12 * D / L ∧ |(z k 1 : ℝ)| ≤ 4 * E / L ∧
        |(z k 1 : ℝ) * k - ((M : ℝ) * E / D) * (z k 0 : ℝ)| ≤ 4 * E / L := by
    have hz : z k ≠ 0 := by intro h; exact (hnonzero k hk).1 (by simpa only [Pi.zero_apply] using congrFun h 0)
    have hb := scaled_vector_bounds M k hM (mem_Icc.mp (hI hk)).2 D E hD hE (z k) hz
    have hleft := div_le_div_of_nonneg_left (show 0 ≤ 12 * D by positivity) hL (hside k hk)
    have hright := div_le_div_of_nonneg_left (show 0 ≤ 4 * E by positivity) hL (hside k hk)
    exact ⟨hb.2.1.trans hleft, hb.2.2.1.trans hright, hb.2.2.2.trans hright⟩
  have hfinite := hcount N hN I (fun k ↦ z k 0) (fun k ↦ z k 1)
    (12 * D / L) (4 * E / L) ((M : ℝ) * E / D) (by positivity) (by positivity)
    (fun k hk ↦ ⟨(mem_Icc.mp (hI hk)).1, (mem_Icc.mp (hI hk)).2.trans (by omega)⟩)
    (fun k hk ↦ ⟨(hnonzero k hk).2.1, (hnonzero k hk).2.2⟩)
    (fun k hk ↦ (hsides k hk).1) (fun k hk ↦ by
      simpa only [Int.cast_mul, Int.cast_natCast] using (hsides k hk).2.2)
  rcases I.eq_empty_or_nonempty with rfl | ⟨k, hk⟩
  · simp only [card_empty, Nat.cast_zero]
    positivity
  · have hA : 1 ≤ 12 * D / L := by
      have habs : (1 : ℝ) ≤ |(z k 0 : ℝ)| := by exact_mod_cast Int.one_le_abs (hnonzero k hk).1
      exact habs.trans (hsides k hk).1
    have hB : 1 ≤ 4 * E / L := by
      have habs : (1 : ℝ) ≤ |(z k 1 : ℝ)| := by exact_mod_cast Int.one_le_abs (hnonzero k hk).2.1
      exact habs.trans (hsides k hk).2.1
    have ha : 2 * (12 * D / L) + 1 ≤ 36 * D / L := by
      calc
        _ ≤ 3 * (12 * D / L) := by linarith only [hA]
        _ = _ := by ring
    have hb : 2 * (4 * E / L) + 1 ≤ 12 * E / L := by
      calc
        _ ≤ 3 * (4 * E / L) := by linarith only [hB]
        _ = _ := by ring
    have hproduct := mul_le_mul ha hb (by positivity) (by positivity : 0 ≤ 36 * D / L)
    calc
      _ ≤ (2 * (12 * D / L) + 1) * (2 * (4 * E / L) + 1) * (N : ℝ) ^ ε := hfinite
      _ ≤ (36 * D / L) * (12 * E / L) * (N : ℝ) ^ ε :=
        mul_le_mul_of_nonneg_right hproduct (Real.rpow_nonneg (Nat.cast_nonneg N) _)
      _ = _ := by field_simp; ring

end PaperP1.RelativeIntervalNonAxisCount
