module

public import PaperP1.Asymptotics.SignedSaddleCostLower
public import PaperP1.Asymptotics.CriticalChannelPowers

/-! # Removing the exact critical signed-mark prefactor from the cost minorant -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SignedSaddleCriticalLower

open Filter PaperP1.SaddleParameters PaperP1.SaddleScales PaperP1.OrdinaryReciprocalPrimeInput
  PaperP1.SignedPrivateDyadicField PaperP1.SignedExactWords

def lowerConstant (C : ℝ) : ℝ := (((2 : ℝ) ^ C)⁻¹) ^ 2 / 64

theorem lowerConstant_pos (C : ℝ) : 0 < lowerConstant C := by unfold lowerConstant; positivity

theorem critical_prefactor {N L : ℕ} {C : ℝ} (hN : 2 ≤ N)
    (hcrit : |(L : ℝ) - Real.log N / Real.log 2| ≤ C) :
    lowerConstant C ≤ (signedMarkRate L 0) ^ 2 * ((N : ℝ) ^ 2 / 4) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp := (div_le_iff₀ hn).mp (PaperP1.CriticalChannelPowers.nominal_lower hN hcrit)
  have hs := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ ((2 : ℝ) ^ C)⁻¹) hp 2
  rw [signedMarkRate_zero]
  unfold lowerConstant
  nlinarith only [hs]

theorem uniform_actual_lower (hinput : EIPInput) (C D : ℝ) (hD : 0 ≤ D) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, ∀ hN : max N₀ 2 ≤ N, ∀ L E : ℕ, ∀ hL : 1 ≤ L,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ((L + E + 2 : ℕ) : ℝ) ≤ D * Real.log N →
      Real.exp (-2 * saddleCutoff 1 (Real.log N) - ε * saddleNu 1 (Real.log N)) ≤
        PaperP1.SignedPrivateField.cost (data (E := E) (by omega : 2 ≤ N) hL) := by
  obtain ⟨NC, hCost⟩ := PaperP1.SignedSaddleCostLower.uniform_actual_lower hinput D hD (ε / 2) (by positivity)
  have hnlog : Tendsto (fun N : ℕ ↦ Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have ht := ((tendsto_saddleNu_atTop (by norm_num : (0 : ℝ) < 1)).const_mul_atTop
    (by positivity : 0 < ε / 2)).comp hnlog
  obtain ⟨NP, hP⟩ := eventually_atTop.mp (ht.eventually (eventually_ge_atTop (-Real.log (lowerConstant C))))
  refine ⟨max NC NP, ?_⟩
  intro N hN L E hL hcrit hwidth
  have hp := hP N (by omega)
  change -Real.log (lowerConstant C) ≤ (ε / 2) * saddleNu 1 (Real.log N) at hp
  have hfactor := critical_prefactor (by omega : 2 ≤ N) hcrit
  have hc := hCost N (by omega) L E hL hwidth
  calc
    _ ≤ Real.exp (Real.log (lowerConstant C) +
        (-2 * saddleCutoff 1 (Real.log N) - (ε / 2) * saddleNu 1 (Real.log N))) :=
      Real.exp_le_exp.mpr (by linarith only [hp])
    _ = lowerConstant C * Real.exp (-2 * saddleCutoff 1 (Real.log N) - (ε / 2) * saddleNu 1 (Real.log N)) := by
      rw [Real.exp_add, Real.exp_log (lowerConstant_pos C)]
    _ ≤ (signedMarkRate L 0) ^ 2 * ((N : ℝ) ^ 2 / 4) *
        Real.exp (-2 * saddleCutoff 1 (Real.log N) - (ε / 2) * saddleNu 1 (Real.log N)) :=
      mul_le_mul_of_nonneg_right hfactor (Real.exp_pos _).le
    _ ≤ _ := hc

end PaperP1.SignedSaddleCriticalLower
