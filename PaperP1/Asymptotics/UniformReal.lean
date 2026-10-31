module

public import PaperP1.Asymptotics.Uniform
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# Real-power meaning of uniform subpolynomiality

Generalizes the reciprocal-power conversion pattern in Paper C,
PaperCV282/LogarithmicWordPowers.lean, commit
b9fa9ba490f201b408a302a86f1594ee620b228b, blob
560b73bebb36aeff4d910f0590578d17bafc01a0, Apache-2.0.
-/

namespace PaperP1.UniformReal

theorem uniformSubpolynomialOn_le_rpow
    {admissible : ℕ → ℕ → Prop} {f : ℕ → ℕ → ℝ}
    (hf : UniformSubpolynomialOn admissible f)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L, admissible N L →
      |f N L| ≤ (N : ℝ) ^ ε := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  obtain ⟨Ncore, hcore⟩ := hf (n + 1) (by omega)
  refine ⟨max Ncore 1, ?_⟩
  intro N hN L hL
  have hNone : (1 : ℝ) ≤ N := by exact_mod_cast (le_max_right Ncore 1).trans hN
  have hroot : |f N L| ≤ (N : ℝ) ^ (1 / (n + 1 : ℝ)) := by
    rw [one_div]
    apply (Real.le_rpow_inv_iff_of_pos (abs_nonneg _) (by positivity)
      (by positivity : (0 : ℝ) < n + 1)).mpr
    have hpower := hcore N ((le_max_left _ _).trans hN) L hL
    rw [show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by norm_cast, Real.rpow_natCast]
    exact hpower
  exact hroot.trans (Real.rpow_le_rpow_of_exponent_le hNone hn.le)

end PaperP1.UniformReal

