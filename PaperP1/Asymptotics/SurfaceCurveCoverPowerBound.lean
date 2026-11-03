module

public import PaperP1.Asymptotics.SurfaceCountParameters

/-! # Actual finite surface-cover bounds at polynomial height give fixed powers of N

These are numerical implications from separate exception, curve-number and
per-curve estimates. No surface or curve counting estimate is assumed as an axiom.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SurfaceCurveCoverPowerBound

theorem height_power (N H : ℕ) (B q r ε : ℝ) (hN : 1 ≤ N) (hB : 0 ≤ B) (hr : 0 ≤ r)
    (hH : (H : ℝ) ≤ B * (N : ℝ) ^ q) (hqr : q * r ≤ ε) :
    (H : ℝ) ^ r ≤ B ^ r * (N : ℝ) ^ ε := by
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  calc
    (H : ℝ) ^ r ≤ (B * (N : ℝ) ^ q) ^ r := Real.rpow_le_rpow (Nat.cast_nonneg H) hH hr
    _ = B ^ r * (N : ℝ) ^ (q * r) := by
      rw [Real.mul_rpow hB (Real.rpow_nonneg (Nat.cast_nonneg N) q), ← Real.rpow_mul (Nat.cast_nonneg N)]
    _ ≤ B ^ r * (N : ℝ) ^ ε := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hNreal hqr) (Real.rpow_nonneg hB r)

theorem two_powers (N H : ℕ) (B q ε α β C₀ C₁ x : ℝ)
    (hN : 1 ≤ N) (hB : 0 ≤ B) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hH : (H : ℝ) ≤ B * (N : ℝ) ^ q) (hαq : q * α ≤ ε) (hβq : q * β ≤ ε)
    (hx : x ≤ C₀ * (H : ℝ) ^ α + C₁ * (H : ℝ) ^ β) :
    x ≤ (C₀ * B ^ α + C₁ * B ^ β) * (N : ℝ) ^ ε := by
  have ha := mul_le_mul_of_nonneg_left (height_power N H B q α ε hN hB hα hH hαq) hC₀
  have hb := mul_le_mul_of_nonneg_left (height_power N H B q β ε hN hB hβ hH hβq) hC₁
  exact hx.trans (by nlinarith [add_le_add ha hb])

theorem finite_cover_bound (N H : ℕ) (B q ε α β γ C A x v t : ℝ)
    (hN : 1 ≤ N) (hHpos : 1 ≤ H) (hB : 0 ≤ B) (hα : 0 ≤ α) (hβγ : 0 ≤ β + γ) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hH : (H : ℝ) ≤ B * (N : ℝ) ^ q) (hαq : q * α ≤ ε) (hβγq : q * (β + γ) ≤ ε)
    (hcover : x ≤ v + t * A * (H : ℝ) ^ γ)
    (hexception : v ≤ C * (H : ℝ) ^ α) (hcurves : t ≤ C * (H : ℝ) ^ β) :
    x ≤ (C * B ^ α + C * A * B ^ (β + γ)) * (N : ℝ) ^ ε := by
  have hpoints : t * A * (H : ℝ) ^ γ ≤ C * (H : ℝ) ^ β * A * (H : ℝ) ^ γ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcurves hA)
      (Real.rpow_nonneg (Nat.cast_nonneg H) γ)
  have hcombined : x ≤ C * (H : ℝ) ^ α + (C * A) * (H : ℝ) ^ (β + γ) := by
    have hHreal : (0 : ℝ) < H := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hHpos)
    have hpow : (H : ℝ) ^ (β + γ) = (H : ℝ) ^ β * (H : ℝ) ^ γ := Real.rpow_add hHreal β γ
    rw [hpow]
    nlinarith
  exact two_powers N H B q ε α (β + γ) C (C * A) x hN hB hα hβγ hC (mul_nonneg hC hA)
    hH hαq hβγq hcombined

end PaperP1.SurfaceCurveCoverPowerBound
