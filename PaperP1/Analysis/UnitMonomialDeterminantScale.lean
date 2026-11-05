module

public import PaperP1.Analysis.GridCurveMinorVanishing
public import PaperP1.Analysis.AffineDeterminantUniformScale

/-! # A polynomial-factor interval scale for the actual monomial determinant

The reciprocal interval length has only a polynomial cost in the family size
and monomial degree. Its grid-height exponent is the exact degree/triangle ratio.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UnitMonomialDeterminantScale

open GridCurveMinorVanishing


def scale (n k N : ℕ) : ℝ :=
  16 * (n : ℝ) ^ 2 * ((k + 1 : ℕ) : ℝ) ^ 2 *
    (N : ℝ) ^ ((((k * n : ℕ) : ℝ)) / ((n * (n - 1) / 2 : ℕ) : ℝ))

theorem prefactor_bound (n : ℕ) (hn : 2 ≤ n) (k : ℕ) :
    (((2 * n : ℕ) : ℝ)) ^ n * ((k + 1 : ℕ) : ℝ) ^ ((n - 1) * n) * (n.factorial : ℝ) ≤
      (8 * (n : ℝ) ^ 2 * ((k + 1 : ℕ) : ℝ) ^ 2) ^ (n * (n - 1) / 2) := by
  let v := n * (n - 1) / 2
  have htwo : 2 * v = n * (n - 1) := Nat.mul_div_cancel' n.even_mul_pred_self.two_dvd
  have hn₁ : n ≤ 2 * v := by
    rw [htwo]
    have hp : 1 ≤ n - 1 := by omega
    nlinarith
  have hfac : (n.factorial : ℝ) ≤ (2 : ℝ) ^ v := by
    exact_mod_cast AffineDeterminantUniformScale.factorial_le_triangle_pow n
  have hpow : (((2 * n : ℕ) : ℝ)) ^ n ≤ (((2 * n : ℕ) : ℝ)) ^ (2 * v) :=
    pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ 2 * n by omega)) hn₁
  calc
    _ ≤ (((2 * n : ℕ) : ℝ)) ^ (2 * v) * ((k + 1 : ℕ) : ℝ) ^ ((n - 1) * n) * (2 : ℝ) ^ v := by
      exact mul_le_mul (mul_le_mul_of_nonneg_right hpow (by positivity)) hfac (Nat.cast_nonneg _) (by positivity)
    _ = (8 * (n : ℝ) ^ 2 * ((k + 1 : ℕ) : ℝ) ^ 2) ^ v := by
      rw [show (n - 1) * n = 2 * v by rw [Nat.mul_comm]; exact htwo.symm, pow_mul, pow_mul, ← mul_pow, ← mul_pow]
      congr 1
      push_cast
      ring

theorem scale_one_le (n : ℕ) (hn : 2 ≤ n) (k N : ℕ) (hN : 0 < N) : 1 ≤ scale n k N := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hkR : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ k + 1 by omega)
  have hc : (1 : ℝ) ≤ 16 * (n : ℝ) ^ 2 * ((k + 1 : ℕ) : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((n : ℝ) - 2), sq_nonneg (((k + 1 : ℕ) : ℝ) - 1)]
  have hr : (1 : ℝ) ≤ (N : ℝ) ^ ((((k * n : ℕ) : ℝ)) / ((n * (n - 1) / 2 : ℕ) : ℝ)) :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ N by omega)) (by positivity)
  exact hc.trans (le_mul_of_one_le_right (zero_le_one.trans hc) hr)

theorem smallness (n : ℕ) (hn : 2 ≤ n) (k N : ℕ) (hN : 0 < N) (δ : ℝ)
    (hδ : 0 ≤ δ) (hscale : δ ≤ 1 / scale n k N) :
    (N : ℝ) ^ (k * n) * analyticBudget n k δ < 1 := by
  let v := n * (n - 1) / 2
  let α := (((k * n : ℕ) : ℝ)) / (v : ℝ)
  let K := 8 * (n : ℝ) ^ 2 * ((k + 1 : ℕ) : ℝ) ^ 2
  let R := (N : ℝ) ^ α
  have hv : 1 ≤ v := (LocalDeterminantDegreeChoice.triangle_weight n hn).1
  have hvR : (0 : ℝ) < v := by exact_mod_cast (show 0 < v by omega)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hK : 0 < K := by dsimp only [K]; positivity
  have hR : 0 < R := Real.rpow_pos_of_pos hNR α
  have hscale_eq : scale n k N = 2 * (K * R) := by
    dsimp only [scale, K, R, α, v]
    ring
  have hhalf : K * R * δ ≤ (1 / 2 : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hscale (mul_pos hK hR).le
    have heq : K * R * (1 / scale n k N) = (1 / 2 : ℝ) := by
      rw [hscale_eq]
      field_simp
    exact hm.trans_eq heq
  have hpower : (N : ℝ) ^ (k * n) = R ^ v := by
    dsimp only [R]
    rw [← Real.rpow_mul_natCast hNR.le, ← Real.rpow_natCast]
    congr 1
    dsimp only [α]
    exact (div_mul_cancel₀ _ hvR.ne').symm
  calc
    _ ≤ R ^ v * (K ^ v * δ ^ v) := by
      rw [hpower]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (prefactor_bound n hn k) (pow_nonneg hδ v)) (pow_nonneg hR.le v)
    _ = (K * R * δ) ^ v := by rw [mul_pow, mul_pow]; ring
    _ ≤ (1 / 2 : ℝ) ^ v := pow_le_pow_left₀ (mul_nonneg (mul_pos hK hR).le hδ) hhalf v
    _ < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)

theorem inverse_scale_bounds (n : ℕ) (hn : 2 ≤ n) (k N : ℕ) (hN : 0 < N) :
    0 < 1 / scale n k N ∧ 1 / scale n k N ≤ 1 := by
  have hh := scale_one_le n hn k N hN
  exact ⟨one_div_pos.mpr (zero_lt_one.trans_le hh), (div_le_one (zero_lt_one.trans_le hh)).mpr hh⟩

end PaperP1.UnitMonomialDeterminantScale
