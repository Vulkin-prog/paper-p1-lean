module

public import PaperP1.Arithmetic.CleanBoundaryReciprocal
public import PaperP1.Analysis.ReciprocalOddPivotDyadicScale
public import PaperP1.Analysis.SaddlePowerErrors
public import PaperP1.Asymptotics.ForcingExceptionLedger

/-! # Restoring the reciprocal mass on the literal clean signed sources -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CleanBoundaryReciprocalLower

open PaperP1.CleanBoundaryReciprocal PaperP1.CleanPivotPairs PaperP1.OddPrimePivot
  PaperP1.SaddleParameters PaperP1.SaddleScales PaperP1.OrdinaryReciprocalPrimeInput

theorem uniform_lower (hinput : EIPInput) (D : ℝ) (hD : 0 ≤ D) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ B Y : ℕ,
      1 ≤ B → (B : ℝ) ≤ D * Real.log N → 1 ≤ Y → (Y : ℝ) ≤ (Real.log N) ^ 5 →
      (N : ℝ) / 2 * Real.exp (-2 * saddleCutoff 1 (Real.log N) - ε * saddleNu 1 (Real.log N)) ≤
        reciprocalSum (sources N B Y) largestOddPrime := by
  obtain ⟨ND, hDyadic⟩ := PaperP1.ReciprocalOddPivotDyadicScale.uniform_dyadic_sandwich hinput ε hε
  obtain ⟨NE, hExceptional⟩ := PaperP1.ForcingExceptionLedger.uniform_exception_counts D hD (1 / 40) (by norm_num)
  obtain ⟨NP, hPower⟩ := PaperP1.SaddlePowerErrors.power_negligible 1 (37 / 40) ε (1 / 4) (by norm_num) (by norm_num)
  refine ⟨max ND (max NE NP), ?_⟩
  intro N hN B Y hB hwidth hY hcut
  have hbad := (hExceptional N (by omega) B Y (2 * N + B) 0 0 hB hwidth hY hcut le_rfl (by omega) (by omega)).1
  norm_num only [show (9 : ℝ) / 10 + 1 / 40 = 37 / 40 by norm_num] at hbad
  have hpow := hPower N (by omega)
  rw [Real.rpow_one] at hpow
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hone : (1 : ℝ) ≤ (N : ℝ) ^ (37 / 40 : ℝ) := Real.one_le_rpow hN1 (by norm_num)
  have hsmall : 1 + (PaperP1.ForcingExceptionalSets.badBoundaries N B Y).card ≤
      (N : ℝ) / 2 * Real.exp (-2 * saddleCutoff 1 (Real.log N) - ε * saddleNu 1 (Real.log N)) := by
    nlinarith only [hbad, hone, hpow]
  have hd := (hDyadic N (by omega)).1
  have hf := finite_lower (by omega : 2 ≤ N) B Y
  nlinarith only [hd, hf, hsmall]

end PaperP1.CleanBoundaryReciprocalLower
