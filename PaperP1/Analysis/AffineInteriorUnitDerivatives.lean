module

public import PaperP1.Analysis.LocalAffineDerivativeFormula
public import PaperP1.Analysis.IteratedDerivativeInteriorBound

/-! # Unit positive-order derivatives after an actual short affine change -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AffineInteriorUnitDerivatives

open Set LocalAffineDerivativeFormula
open scoped ContDiff

theorem scaled_power_bound (c A : ℝ) (hc : 0 ≤ c) (hcone : c ≤ 1)
    (hA : 0 ≤ A) (hprod : c * A ≤ 1) (j : ℕ) (hj : 1 ≤ j) :
    c ^ j * A ^ (j - 1) ≤ 1 := by
  have hpow : c ^ j = c ^ (j - 1) * c := by
    rw [← pow_succ, show j - 1 + 1 = j by omega]
  calc
    _ = c * (c * A) ^ (j - 1) := by rw [hpow, mul_pow]; ring
    _ ≤ c * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ (mul_nonneg hc hA) hprod) hc
    _ = c := mul_one c
    _ ≤ 1 := hcone

theorem positive_unit_derivative (f : ℝ → ℝ) (a b δ : ℝ) (hδ : 0 < δ) (r : ℕ)
    (hf : ContDiffOn ℝ ∞ f (Ioo a b))
    (hfirst : ∀ x ∈ Ioo a b, |deriv f x| ≤ 1)
    (hmono : ∀ n ≤ r, MonotoneOn (iteratedDeriv n f) (Ioo a b) ∨
      AntitoneOn (iteratedDeriv n f) (Ioo a b))
    (u c : ℝ) (hc : 0 ≤ c) (hcone : c ≤ 1)
    (hscale : c ≤ δ / (2 * ((r + 1 : ℕ) : ℝ)))
    (j : ℕ) (hj : 1 ≤ j) (hjr : j ≤ r) (t : ℝ)
    (hleft : a + δ ≤ parameter u c t) (hright : parameter u c t ≤ b - δ) :
    |iteratedDeriv j (fun v ↦ f (parameter u c v)) t| ≤ 1 := by
  have hmem : parameter u c t ∈ Ioo a b := ⟨by linarith, by linarith⟩
  have hformula := LocalAffineDerivativeFormula.iterated_formula f a b hf u c j hmem
  have hbound := IteratedDerivativeInteriorBound.interior_bound f a b δ hδ r hf hfirst hmono
    j hj hjr (parameter u c t) hleft hright
  have hR : (0 : ℝ) < 2 * ((r + 1 : ℕ) : ℝ) := by positivity
  have hmul : c * (2 * ((r + 1 : ℕ) : ℝ)) ≤ δ := (le_div_iff₀ hR).mp hscale
  have hprod : c * (2 * ((r + 1 : ℕ) : ℝ) / δ) ≤ 1 := by
    rw [← mul_div_assoc]
    exact (div_le_one hδ).mpr hmul
  rw [hformula, abs_mul, abs_of_nonneg (pow_nonneg hc j)]
  exact (mul_le_mul_of_nonneg_left hbound (pow_nonneg hc j)).trans
    (scaled_power_bound c (2 * ((r + 1 : ℕ) : ℝ) / δ) hc hcone (by positivity) hprod j hj)

end PaperP1.AffineInteriorUnitDerivatives
