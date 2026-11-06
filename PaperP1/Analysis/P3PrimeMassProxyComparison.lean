module

public import PaperP1.Analysis.P3PrimeMassProxy
public import PaperP1.Analysis.P3CoefficientLogBudget
public import PaperP1.Analysis.P3SmoothGlobalDivisorEstimate
public import PaperP1.Arithmetic.CertificatePrimeWindow

/-! # Polynomial coefficient and exceptional-certificate heights give the explicit uniform prime-mass proxy -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3PrimeMassProxyComparison

open Finset P3StandardMonomialParameters

theorem value_le_lowerBound (d e A H T₀ c₀ T₁ c₁ K : ℕ)
    (hd : 0 < d) (hA : 0 < A) (hH : 1 ≤ H) (hT₀ : 0 < T₀) (hT₁ : 0 < T₁)
    (hK : 0 < K) (he : 1 ≤ e) (hKe : K ≤ e)
    (z : ℤ) (hz : z ≠ 0) (hzbound : z.natAbs ≤ T₀ * H ^ c₀) (hAbound : A ≤ T₁ * H ^ c₁)
    (D γ : ℝ) (hlog : Real.log (H : ℝ) ≤ γ * Real.log (e : ℝ)) :
    P3PrimeMassProxy.value d D γ ((2 / 3 : ℝ) * c₀ + c₁ + ((d - 1 : ℕ) : ℝ))
      ((2 / 3 : ℝ) * Real.log (T₀ : ℝ) +
        Real.log ((Fintype.card (P3HomogeneousCoefficientFamily.Index (d - 1)) * (d * T₁) : ℕ) : ℝ)) K e ≤
      P3SmoothGlobalDivisorEstimate.lowerBound d (size d e) A H D K (CertificatePrimeWindow.primes K e z) := by
  let s := size d e
  let R := Real.sqrt (2 * (s : ℝ) / D)
  let r : ℝ := (2 / 3 : ℝ) * c₀ + c₁ + ((d - 1 : ℕ) : ℝ)
  let B : ℝ := (2 / 3 : ℝ) * Real.log (T₀ : ℝ) +
    Real.log ((Fintype.card (P3HomogeneousCoefficientFamily.Index (d - 1)) * (d * T₁) : ℕ) : ℝ)
  let S := CertificatePrimeWindow.primes K e z
  have hm := CertificatePrimeWindow.bounded_mass_lower_bound K e hK he hKe z hz T₀ H c₀ hT₀ hH hzbound
  have hc := P3CoefficientLogBudget.gradient_log_bound d T₁ c₁ A H hd hT₁ hA hH hAbound
  simp only [Nat.cast_add] at hc
  have hcdiv := div_le_div_of_nonneg_right hc (Nat.cast_nonneg K)
  have hmain := sub_le_sub
    (mul_le_mul_of_nonneg_left hm (show (0 : ℝ) ≤ 2 / 3 by norm_num)) hcdiv
  have hr : 0 ≤ r := by dsimp only [r]; positivity
  have hpositive : 0 ≤ r * (γ * Real.log (e : ℝ) - Real.log (H : ℝ)) / K :=
    div_nonneg (mul_nonneg hr (sub_nonneg.mpr hlog)) (Nat.cast_nonneg K)
  have halgebra :
      (2 / 3 : ℝ) * (Real.log (e : ℝ) - SurfaceDeterminantPrimeWindow.cost K -
        (Real.log (T₀ : ℝ) + (c₀ : ℝ) * Real.log (H : ℝ)) / K) -
      (Real.log ((Fintype.card (P3HomogeneousCoefficientFamily.Index (d - 1)) * (d * T₁) : ℕ) : ℝ) +
        ((c₁ : ℝ) + ((d - 1 : ℕ) : ℝ)) * Real.log (H : ℝ)) / K =
      (((2 / 3 : ℝ) - r * γ / K) * Real.log (e : ℝ) -
        (2 / 3 : ℝ) * SurfaceDeterminantPrimeWindow.cost K - B / K) +
        r * (γ * Real.log (e : ℝ) - Real.log (H : ℝ)) / K := by
    dsimp only [r, B]
    ring
  have hbracket :
      ((2 / 3 : ℝ) - r * γ / K) * Real.log (e : ℝ) -
        (2 / 3 : ℝ) * SurfaceDeterminantPrimeWindow.cost K - B / K ≤
      (2 / 3 : ℝ) * CertificatePrimeWindow.mass K e z -
        (Real.log ((Fintype.card (P3HomogeneousCoefficientFamily.Index (d - 1)) * (d * A) : ℕ) : ℝ) +
          ((d - 1 : ℕ) : ℝ) * Real.log (H : ℝ)) / K := by
    calc
      _ ≤ _ + r * (γ * Real.log (e : ℝ) - Real.log (H : ℝ)) / K := le_add_of_nonneg_right hpositive
      _ = _ := halgebra.symm
      _ ≤ _ := hmain
  have hscale := mul_le_mul_of_nonneg_left hbracket (show 0 ≤ R * (s : ℝ) by positivity)
  have htheta := mul_le_mul_of_nonneg_left (CertificatePrimeWindow.theta_upper_bound K e z)
    (show 0 ≤ 3 * (s : ℝ) by positivity)
  have hh := sub_le_sub hscale htheta
  dsimp only [P3PrimeMassProxy.value, P3SmoothGlobalDivisorEstimate.lowerBound]
  convert hh using 1
  · dsimp only [r, B, R, s]
    ring
  · dsimp only [R, s, CertificatePrimeWindow.mass]
    ring

end PaperP1.P3PrimeMassProxyComparison
