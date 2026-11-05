module

public import PaperP1.Analysis.ElementaryDyadicPivotLower
public import PaperP1.Arithmetic.CleanBoundaryReciprocal
public import PaperP1.Asymptotics.ForcingExceptionLedger

/-! # An unconditional power-scale reciprocal lower bound on actual clean sources -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ElementaryCleanPivotLower

open CleanBoundaryReciprocal CleanPivotPairs OddPrimePivot

theorem uniform_lower (D : ℝ) (hD : 0 ≤ D) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ B Y : ℕ,
      1 ≤ B → (B : ℝ) ≤ D * Real.log N → 1 ≤ Y → (Y : ℝ) ≤ (Real.log N) ^ 5 →
      (N : ℝ) ^ (1 - ε) ≤ reciprocalSum (sources N B Y) largestOddPrime := by
  let η := min (ε / 2) (1 / 80)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hηε : η ≤ ε / 2 := min_le_left _ _
  have hηsmall : η ≤ 1 / 80 := min_le_right _ _
  obtain ⟨ND, hND, hd⟩ := ElementaryDyadicPivotLower.uniform_lower η hη
  obtain ⟨NE, he⟩ := ForcingExceptionLedger.uniform_exception_counts D hD (1 / 40) (by norm_num)
  obtain ⟨NS, hs⟩ := HalfCountSchedule.factor_absorption 4 (37 / 40) (3 / 40 - η) (by linarith only [hηsmall])
  obtain ⟨NT, ht⟩ := HalfCountSchedule.factor_absorption 2 (1 - ε) (ε - η) (by linarith only [hε, hηε])
  refine ⟨2 + ND + NE + NS + NT, by omega, ?_⟩
  intro N hN B Y hB hwidth hY hcut
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hbad := (he N (by omega) B Y (2 * N + B) 0 0 hB hwidth hY hcut le_rfl (by omega) (by omega)).1
  norm_num only [show (9 : ℝ) / 10 + 1 / 40 = 37 / 40 by norm_num] at hbad
  have hone : (1 : ℝ) ≤ (N : ℝ) ^ (37 / 40 : ℝ) := Real.one_le_rpow hn1 (by norm_num)
  have hrest : 2 * (1 + (ForcingExceptionalSets.badBoundaries N B Y).card) ≤ (N : ℝ) ^ (1 - η) := by
    have hh := hs N (by omega)
    rw [show (37 / 40 : ℝ) + (3 / 40 - η) = 1 - η by ring] at hh
    linarith only [hbad, hone, hh]
  have htarget := ht N (by omega)
  rw [show (1 - ε) + (ε - η) = 1 - η by ring] at htarget
  have hraw := hd N (by omega)
  have hfinite := finite_lower (by omega : 2 ≤ N) B Y
  linarith only [hrest, htarget, hraw, hfinite]

end PaperP1.ElementaryCleanPivotLower
