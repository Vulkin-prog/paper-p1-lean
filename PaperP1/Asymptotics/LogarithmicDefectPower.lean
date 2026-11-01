module

public import PaperP1.Asymptotics.ExpSqrtLog
public import PaperP1.Asymptotics.UniformReal

/-! # A uniform binary power bound from logarithm-over-loglog defect counts -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LogarithmicDefectPower

theorem uniform_power (K ε : ℝ) (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ m : ℕ,
      (m : ℝ) ≤ K * Real.log N / Real.log (Real.log N) → (2 ^ m : ℝ) ≤ (N : ℝ) ^ ε := by
  let admissible := fun N m : ℕ ↦ (m : ℝ) ≤ K * Real.log N / Real.log (Real.log N)
  have hsub := ExpSqrtLog.uniformSubpolynomialOn_two_pow_log_div_loglog admissible
    (fun _ m ↦ m) K hK (fun _ _ h ↦ h)
  obtain ⟨N₀, hN₀⟩ := UniformReal.uniformSubpolynomialOn_le_rpow hsub ε hε
  refine ⟨N₀, ?_⟩
  intro N hN m hm
  simpa only [Nat.cast_pow, Nat.cast_ofNat, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ m)] using hN₀ N hN m hm

end PaperP1.LogarithmicDefectPower
