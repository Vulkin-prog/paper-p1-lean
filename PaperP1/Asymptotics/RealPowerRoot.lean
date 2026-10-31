module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-
Adapted from PaperCV282/HostRealPowers.lean, by Vulkin-prog, Apache-2.0.
Source commit b9fa9ba490f201b408a302a86f1594ee620b228b,
Git blob d00caddc1443822afe08f449437da5cf1bc67545.
Only le_rpow_div_of_pow_le; host-counting development excluded.
-/

@[expose] public section

namespace PaperP1.HostRealPowers

/-- Taking a positive integer root of a natural-power inequality. -/
theorem le_rpow_div_of_pow_le {a M : ℝ} (ha : 0 ≤ a) (hM : 0 ≤ M)
    {p q : ℕ} (hq : 0 < q) (h : a ^ q ≤ M ^ p) :
    a ≤ M ^ ((p : ℝ) / q) := by
  have hroot : a ≤ (M ^ p) ^ ((q : ℝ)⁻¹) := by
    apply (Real.le_rpow_inv_iff_of_pos ha (by positivity)
      (by exact_mod_cast hq)).mpr
    simpa only [Real.rpow_natCast] using h
  simpa only [← Real.rpow_natCast M p, ← Real.rpow_mul hM, div_eq_mul_inv] using hroot


end PaperP1.HostRealPowers

