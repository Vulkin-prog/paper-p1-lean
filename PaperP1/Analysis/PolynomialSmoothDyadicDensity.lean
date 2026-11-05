module

public import PaperP1.Analysis.PolynomialSmoothDensity
public import PaperP1.Arithmetic.OrdinarySmoothDyadicDensity
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Positive ordinary smooth density in actual dyadic intervals

For every fixed exponent alpha>0, a fixed positive proportion of [N,2N)
consists of ordinary N^alpha-smooth integers. The density is not claimed to
be the Dickman value, and no logarithmic short-interval asymptotic is used.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PolynomialSmoothDyadicDensity

open Filter OrdinarySmoothDyadicDensity

theorem uniform_lower (α : ℝ) (hα : 0 < α) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2,
      δ * (N : ℝ) ≤ (dyadicSmooth N ⌊(N : ℝ) ^ α⌋₊).card := by
  obtain ⟨δ₀, hδ₀, NF, hf⟩ := PolynomialSmoothDensity.uniform_lower α hα
  let J := ⌈2 / δ₀⌉₊
  have hpow : 2 / δ₀ ≤ (((2 : ℕ) ^ J : ℕ) : ℝ) := by
    have hj : 2 / δ₀ ≤ (J : ℝ) := Nat.le_ceil _
    have hh : (J : ℝ) ≤ (((2 : ℕ) ^ J : ℕ) : ℝ) := by exact_mod_cast (show J < 2 ^ J from Nat.lt_two_pow_self).le
    exact hj.trans hh
  have hJ : 1 / (((2 : ℕ) ^ J : ℕ) : ℝ) ≤ δ₀ / 2 := by
    have hh := (div_le_iff₀ hδ₀).mp hpow
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (((2 : ℕ) ^ J : ℕ) : ℝ))).mpr
    nlinarith only [hh]
  have ht : Tendsto (fun N : ℕ ↦ (N : ℝ) ^ α) atTop atTop :=
    (tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop
  obtain ⟨NY, hy⟩ := eventually_atTop.mp (ht.eventually (eventually_ge_atTop (2 : ℝ)))
  refine ⟨δ₀ / (2 * ((J : ℝ) + 1)), by positivity, max NF NY, ?_⟩
  intro N hN
  have hY : 2 ≤ ⌊(N : ℝ) ^ α⌋₊ :=
    (Nat.le_floor_iff (Real.rpow_nonneg (Nat.cast_nonneg N) α)).mpr (hy N (by omega))
  exact density_transfer N _ J (by omega) hY δ₀ (hf N (by omega)) hJ

end PaperP1.PolynomialSmoothDyadicDensity
