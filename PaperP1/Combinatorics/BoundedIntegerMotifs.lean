module

public import PaperP1.Combinatorics.BoundedSubsetWeights
public import Mathlib.Data.Int.Interval

/-! # Counting actual bounded integer motifs without choosing their order -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BoundedIntegerMotifs

open Finset PaperP1.BoundedSubsetWeights

def offsets (W : ℕ) : Finset ℤ := Icc (-(W : ℤ)) W

theorem offsets_card (W : ℕ) : (offsets W).card = 2 * W + 1 := by
  rw [offsets, Int.card_Icc]
  omega

theorem subset_offsets (W : ℕ) (A : Finset ℤ) : A ⊆ offsets W ↔ ∀ a ∈ A, a.natAbs ≤ W := by
  constructor
  · intro h a ha
    have habs : |a| ≤ (W : ℤ) := abs_le.mpr (mem_Icc.mp (h ha))
    rw [Int.abs_eq_natAbs] at habs
    exact_mod_cast habs
  · intro h a ha
    have habs : |a| ≤ (W : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast h a ha
    exact mem_Icc.mpr (abs_le.mp habs)

theorem bounded_count (W m : ℕ) :
    ((boundedSubsets (offsets W) m).card : ℝ) ≤ (2 * W + 2 : ℝ) ^ m * Real.exp 1 := by
  let P := offsets W
  have hcard : ((boundedSubsets P m).card : ℝ) = weightSum P 1 m := by simp [weightSum]
  have hbase : (1 : ℝ) ≤ P.card + 1 := le_add_of_nonneg_left (Nat.cast_nonneg P.card)
  have hbound := weightSum_le P 1 (P.card + 1) m (by norm_num) hbase
  have hratio : (P.card : ℝ) / (P.card + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  calc
    _ = weightSum P 1 m := hcard
    _ ≤ (P.card + 1 : ℝ) ^ m * Real.exp ((P.card : ℝ) / (P.card + 1)) := by simpa only [one_mul] using hbound
    _ ≤ (P.card + 1 : ℝ) ^ m * Real.exp 1 :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hratio) (by positivity)
    _ = _ := by dsimp [P]; rw [offsets_card]; push_cast; ring

end PaperP1.BoundedIntegerMotifs
