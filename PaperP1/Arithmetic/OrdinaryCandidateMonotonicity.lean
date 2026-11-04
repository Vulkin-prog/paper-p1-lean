module

public import PaperP1.Arithmetic.NonanchorPivotSelection
public import PaperP1.Model.ForcingExceptionalSets

/-! # Exact ordinary smooth-candidate comparison between short and actual words -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OrdinaryCandidateMonotonicity

open Finset PaperP1.Arithmetic PaperP1.NonanchorPivotSelection PaperP1.ForcingExceptionalSets

theorem card_le {j B B' : ℕ} {Q Q' : ℝ} (hB : B ≤ B') (hQ : Q ≤ Q') :
    (ordinaryIndices j B Q).card ≤ (ordinaryIndices j B' Q').card := by
  classical
  apply card_le_card_of_injOn (Fin.castLE hB)
  · intro i hi
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hi).2.trans hQ⟩
  · intro i _ k _ h
    exact Fin.ext (congrArg (fun z : Fin B' ↦ z.val) h)

theorem boundary_lt_two_mul {N j : ℕ} (hN : 2 ≤ N) (hj : j ∈ boundaryBlock N) : j < 2 * N := by
  have h := mem_Ico.mp ((mem_boundaryBlock hN).mp hj)
  omega

theorem smooth_threshold {N j : ℕ} (hN : 2 ≤ N) (hj : j ≤ 2 * N) {a : ℝ} (ha : 0 ≤ a) :
    (j : ℝ) ^ (a / 2) ≤ (N : ℝ) ^ a := by
  have hbase : (j : ℝ) ≤ (N : ℝ) ^ 2 := by
    exact_mod_cast hj.trans (by simpa only [pow_two] using Nat.mul_le_mul_right N hN)
  calc
    _ ≤ ((N : ℝ) ^ 2) ^ (a / 2) := Real.rpow_le_rpow (Nat.cast_nonneg j) hbase (by linarith)
    _ = (N : ℝ) ^ a := by
      rw [← Real.rpow_two, ← Real.rpow_mul (Nat.cast_nonneg N)]
      congr 1
      ring

end PaperP1.OrdinaryCandidateMonotonicity
