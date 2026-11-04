module

public import PaperP1.Asymptotics.SignedSaddleCriticalLower
public import PaperP1.Asymptotics.SignedSaddleExcess

/-! # The prescribed signed forcing has the sharp logarithmic lower cost

This is a lower bound for this specified positive coordinate cost. It
does not give a lower bound for dependence or total variation distance.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SignedPrescribedSaddleLower

open PaperP1.SaddleParameters PaperP1.SaddleScales PaperP1.OrdinaryReciprocalPrimeInput
  PaperP1.SignedPrivateDyadicField PaperP1.SignedSaddleExcess

theorem uniform_actual_lower (hinput : EIPInput) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, ∀ hN : max N₀ 2 ≤ N, ∀ L : ℕ, ∀ hL : 1 ≤ L,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      Real.exp (-2 * saddleCutoff 1 (Real.log N) - ε * saddleNu 1 (Real.log N)) ≤
        PaperP1.SignedPrivateField.cost (data (E := excess N) (by omega : 2 ≤ N) hL) := by
  obtain ⟨NW, hW⟩ := uniform_width C
  obtain ⟨NC, hC⟩ := PaperP1.SignedSaddleCriticalLower.uniform_actual_lower hinput C widthConstant widthConstant_pos.le ε hε
  refine ⟨max NW NC, ?_⟩
  intro N hN L hL hcrit
  exact hC N (by omega) L (excess N) hL hcrit (hW N (by omega) L hcrit)

theorem uniform_power_obstruction (hinput : EIPInput) (C α K : ℝ) (hα : 0 < α) (hK : 0 < K) :
    ∃ N₀ : ℕ, ∀ N : ℕ, ∀ hN : max N₀ 2 ≤ N, ∀ L : ℕ, ∀ hL : 1 ≤ L,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      K * (N : ℝ) ^ (-α) ≤
        PaperP1.SignedPrivateField.cost (data (E := excess N) (by omega : 2 ≤ N) hL) := by
  obtain ⟨NC, hC⟩ := uniform_actual_lower hinput C 1 (by norm_num)
  obtain ⟨NP, hP⟩ := PaperP1.SaddlePowerErrors.power_negligible 0 (-α) 1 (1 / K) (by linarith) (by positivity)
  refine ⟨max NC NP, ?_⟩
  intro N hN L hL hcrit
  have hp := hP N (by omega)
  simp only [Real.rpow_zero, mul_one, one_mul] at hp
  have hp' := mul_le_mul_of_nonneg_left hp hK.le
  have he : K * (1 / K * Real.exp (-2 * saddleCutoff 1 (Real.log N) - saddleNu 1 (Real.log N))) =
      Real.exp (-2 * saddleCutoff 1 (Real.log N) - saddleNu 1 (Real.log N)) := by field_simp
  rw [he] at hp'
  have hc := hC N (by omega) L hL hcrit
  simp only [one_mul] at hc
  exact hp'.trans hc

end PaperP1.SignedPrescribedSaddleLower
