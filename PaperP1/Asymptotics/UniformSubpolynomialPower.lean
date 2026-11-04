module

public import PaperP1.Asymptotics.Uniform
public import PaperP1.Asymptotics.RealPowerRoot

/-! # Literal real-power bounds from the exact uniform reciprocal-power convention -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UniformSubpolynomialPower

theorem bound {admissible : ℕ → ℕ → Prop} {f : ℕ → ℕ → ℝ}
    (hf : PaperP1.UniformSubpolynomialOn admissible f) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L, admissible N L → |f N L| ≤ (N : ℝ) ^ ε := by
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  obtain ⟨NF, hF⟩ := hf (k + 1) (by omega)
  refine ⟨max NF 1, ?_⟩
  intro N hN L hNL
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hpow : |f N L| ^ (k + 1) ≤ (N : ℝ) ^ 1 := by simpa only [pow_one] using hF N (by omega) L hNL
  have hroot := PaperP1.HostRealPowers.le_rpow_div_of_pow_le (abs_nonneg (f N L))
    (Nat.cast_nonneg N) (by omega : 0 < k + 1) hpow
  exact hroot.trans (Real.rpow_le_rpow_of_exponent_le hn (by exact_mod_cast hk.le))

end PaperP1.UniformSubpolynomialPower
