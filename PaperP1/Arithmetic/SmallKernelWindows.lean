module

public import PaperP1.Arithmetic.RankinSmallKernel

/-! # Actual dyadic windows containing a value with bounded large odd kernel -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmallKernelWindows

open Finset PaperP1.LargeOddKernel PaperP1.RankinSmallKernel

def windows (N B : ℕ) (T : ℝ) : Finset ℕ :=
  (Finset.Ico N (2 * N)).filter fun x ↦
    ∃ i : Fin B, (largeOddKernel B (x - 1 + i.val) : ℝ) ≤ T

def placements (B n : ℕ) : Finset ℕ :=
  (univ : Finset (Fin B)).image fun i ↦ n + 1 - i.val

theorem windows_cover {N B : ℕ} (T : ℝ) (hN : 2 ≤ N) (hB : B ≤ N) :
    windows N B T ⊆ (values (3 * N) B T).biUnion (placements B) := by
  intro x hx
  obtain ⟨hx, i, hT⟩ := mem_filter.mp hx
  obtain ⟨hxlo, hxhi⟩ := mem_Ico.mp hx
  let n := x - 1 + i.val
  have hi := i.isLt
  have heq : truncatedKernel (B : ℝ) n = largeOddKernel B n := by
    simpa only [Nat.floor_natCast] using truncatedKernel_eq_floor (B : ℝ) (Nat.cast_nonneg B) n
  have hn : n ∈ values (3 * N) B T := by
    apply (mem_values _ _ _ (by positivity) n).mpr
    refine ⟨by dsimp [n]; omega, ?_, ?_⟩
    · have hn : n ≤ 3 * N := by dsimp [n]; omega
      exact_mod_cast hn
    · rw [heq]
      exact hT
  refine mem_biUnion.mpr ⟨n, hn, mem_image.mpr ⟨i, mem_univ _, ?_⟩⟩
  dsimp [n]
  omega

theorem windows_card {N B : ℕ} (T : ℝ) (hN : 2 ≤ N) (hB : B ≤ N) :
    (windows N B T).card ≤ B * (values (3 * N) B T).card := by
  calc
    _ ≤ ((values (3 * N) B T).biUnion (placements B)).card := card_le_card (windows_cover T hN hB)
    _ ≤ ∑ n ∈ values (3 * N) B T, (placements B n).card := card_biUnion_le
    _ ≤ ∑ _n ∈ values (3 * N) B T, B := by
      apply sum_le_sum
      intro n _
      exact card_image_le.trans_eq (by simp)
    _ = _ := by simp only [sum_const, nsmul_eq_mul, Nat.cast_id]; ring

theorem finite_exp_bound {N B : ℕ} (T : ℝ) (hN : 2 ≤ N) (hB : B ≤ N) (hT : 0 ≤ T) :
    ((windows N B T).card : ℝ) ≤
      2 * B * Real.sqrt (3 * N) * Real.sqrt T * Real.exp (2 * Real.sqrt B) := by
  have hcast : ((windows N B T).card : ℝ) ≤
      (B : ℝ) * ((values (3 * N) B T).card : ℝ) := by exact_mod_cast windows_card T hN hB
  refine hcast.trans ?_
  have h := mul_le_mul_of_nonneg_left
    (rankin_half (3 * N) B T (by positivity) (Nat.cast_nonneg B) hT) (Nat.cast_nonneg B)
  convert h using 1; ring

end PaperP1.SmallKernelWindows
