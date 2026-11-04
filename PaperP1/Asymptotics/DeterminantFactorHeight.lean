module

public import PaperP1.Algebra.BivariateFactorHeight
public import PaperP1.Algebra.IrreduciblePointFactor

/-! # One polynomial height exponent for every actual integer auxiliary factor -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DeterminantFactorHeight

open Polynomial PaperP1.BivariateDegrees PaperP1.BivariateHeight

def factorConstant (A B : ℕ) : ℕ := 2 ^ (A + B) * ((A + 1) * (B + 1))

theorem integer_factor_height (A B : ℕ) (F G : ℤ[X][X]) (hF : F ≠ 0) (hG : G ∣ F)
    (hx : degreeX F ≤ A) (hy : degreeY F ≤ B) : height G ≤ factorConstant A B * height F := by
  obtain ⟨R, hR⟩ := hG
  have h := BivariateFactorHeight.companion_T9_4_factor_and_quotient F G R hF hR
  have hp : (height G : ℝ) ≤ (2 : ℝ) ^ (degreeX F + degreeY F) *
      Real.sqrt (((degreeX F + 1) * (degreeY F + 1) : ℕ) : ℝ) * height F := h.1.trans h.2.2
  have hpow : (2 : ℝ) ^ (degreeX F + degreeY F) ≤ (2 : ℝ) ^ (A + B) :=
    pow_le_pow_right₀ (by norm_num) (Nat.add_le_add hx hy)
  have hrect : (degreeX F + 1) * (degreeY F + 1) ≤ (A + 1) * (B + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hH : (1 : ℝ) ≤ (((A + 1) * (B + 1) : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ (A + 1) * (B + 1) from Nat.one_le_iff_ne_zero.mpr (by positivity))
  have hsqrt : Real.sqrt (((degreeX F + 1) * (degreeY F + 1) : ℕ) : ℝ) ≤
      (((A + 1) * (B + 1) : ℕ) : ℝ) := by
    exact (Real.sqrt_le_sqrt (by exact_mod_cast hrect)).trans (Real.sqrt_le_self_iff.mpr (Or.inr hH))
  have hfinal := mul_le_mul_of_nonneg_right
    (mul_le_mul hpow hsqrt (Real.sqrt_nonneg _) (by positivity)) (Nat.cast_nonneg (height F) : (0 : ℝ) ≤ height F)
  have hbound : (height G : ℝ) ≤ (factorConstant A B * height F : ℕ) := hp.trans (by
    simpa only [factorConstant, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hfinal)
  exact_mod_cast hbound

theorem uniform_factor_height (Amax B κ : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ F G : ℤ[X][X], F ≠ 0 → G ∣ F →
      degreeX F ≤ Amax → degreeY F ≤ B → height F ≤ N ^ κ →
      height G ≤ N ^ (κ + 1) ∧ degreeX G ≤ Amax ∧ degreeY G ≤ B := by
  refine ⟨max 1 (factorConstant Amax B), ?_⟩
  intro N hN F G hF hG hx hy hheight
  have hc : factorConstant Amax B ≤ N := by omega
  have hfactor := integer_factor_height Amax B F G hF hG hx hy
  have hdeg := IrreduciblePointFactor.factor_partial_degrees F G hF hG
  refine ⟨hfactor.trans ?_, hdeg.1.trans hx, hdeg.2.trans hy⟩
  calc
    factorConstant Amax B * height F ≤ N * N ^ κ := Nat.mul_le_mul hc hheight
    _ = N ^ (κ + 1) := (pow_succ' N κ).symm

end PaperP1.DeterminantFactorHeight
