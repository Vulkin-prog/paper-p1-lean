module

public import PaperP1.Analysis.P3GlobalDeterminantScaleLimits
public import PaperP1.Analysis.P3StandardFactorialLimits
public import PaperP1.Arithmetic.SurfaceDeterminantPrimeWindow

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3PrimeMassProxy

open Filter Topology P3StandardMonomialParameters

def value (d : ℕ) (D γ r B : ℝ) (K e : ℕ) : ℝ :=
  Real.sqrt (2 * (size d e : ℝ) / D) * (size d e : ℝ) *
    (((2 / 3 : ℝ) - r * γ / K) * Real.log (e : ℝ) -
      (2 / 3 : ℝ) * SurfaceDeterminantPrimeWindow.cost K - B / K) -
    3 * (size d e : ℝ) * (e : ℝ) * Real.log 4

theorem value_ratio (d : ℕ) (D γ r B : ℝ) (hD : 0 < D) (K : ℕ) :
    Tendsto (fun e : ℕ ↦ value d D γ r B K e / ((e : ℝ) ^ 3 * Real.log (e : ℝ))) atTop
      (𝓝 (((2 / 3 : ℝ) - r * γ / K) * (Real.sqrt ((d : ℝ) / D) * ((d : ℝ) / 2)))) := by
  let a : ℝ := (2 / 3 : ℝ) - r * γ / K
  let C : ℝ := (2 / 3 : ℝ) * SurfaceDeterminantPrimeWindow.cost K + B / K
  have h := (((P3GlobalDeterminantScaleLimits.main_scale_ratio d D hD).const_mul a).sub
    (P3GlobalDeterminantScaleLimits.constant_error_ratio d D C hD)).sub
      (P3GlobalDeterminantScaleLimits.theta_error_ratio d)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with e he
  have he0 : (e : ℝ) ≠ 0 := by exact_mod_cast (show e ≠ 0 by omega)
  have hl0 : Real.log (e : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast (show 1 < e by omega))).ne'
  change a * (Real.sqrt (2 * (size d e : ℝ) / D) * (size d e : ℝ) / (e : ℝ) ^ 3) -
    C * Real.sqrt (2 * (size d e : ℝ) / D) * (size d e : ℝ) / ((e : ℝ) ^ 3 * Real.log (e : ℝ)) -
    3 * (size d e : ℝ) * (e : ℝ) * Real.log 4 / ((e : ℝ) ^ 3 * Real.log (e : ℝ)) = _
  dsimp only [value, a, C]
  field_simp [he0, hl0]
  ring

theorem exists_gap_parameters (d : ℕ) (hd : 0 < d) (D γ r B : ℝ) (hD : 0 < D)
    (hγ : γ < Real.sqrt ((d : ℝ) / D)) (Kmin : ℕ) :
    ∃ K : ℕ, Kmin ≤ K ∧ 2 ≤ K ∧ ∃ E₀ : ℕ, d ≤ E₀ ∧ K ≤ E₀ ∧ 2 ≤ E₀ ∧
      ∀ e ≥ E₀, Real.log ((size d e).factorial : ℝ) + γ * (weight d e : ℝ) * Real.log (e : ℝ) <
        value d D γ r B K e := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  let c := Real.sqrt ((d : ℝ) / D) * ((d : ℝ) / 2)
  have hc : γ * ((d : ℝ) / 3) < (2 / 3 : ℝ) * c := by
    dsimp only [c]
    nlinarith
  have hi : Tendsto (fun K : ℕ ↦ (K : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hlim := ((tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (2 / 3 : ℝ)) atTop (𝓝 (2 / 3 : ℝ))).sub
    (hi.const_mul (r * γ))).mul_const c
  simp only [mul_zero, sub_zero] at hlim
  have hev := hlim.eventually (Ioi_mem_nhds hc)
  obtain ⟨K, hKval, hKmin⟩ := (hev.and (eventually_ge_atTop (max Kmin 2))).exists
  have hgap : 0 < ((2 / 3 : ℝ) - r * γ / K) * c - γ * ((d : ℝ) / 3) := by
    change γ * ((d : ℝ) / 3) < ((2 / 3 : ℝ) - (r * γ) * (K : ℝ)⁻¹) * c at hKval
    simpa only [div_eq_mul_inv] using sub_pos.mpr hKval
  have h := ((value_ratio d D γ r B hD K).sub
    ((P3StandardMonomialLimits.weight_ratio d).const_mul γ)).sub
      (P3StandardFactorialLimits.factorial_logarithmic_ratio d)
  simp only [sub_zero] at h
  have hpos := h.eventually (Ioi_mem_nhds hgap)
  obtain ⟨E₁, hE₁⟩ := eventually_atTop.mp hpos
  let E₀ := max E₁ (max d (max K 2))
  refine ⟨K, (le_max_left Kmin 2).trans hKmin, (le_max_right Kmin 2).trans hKmin,
    E₀, ?_, ?_, ?_, ?_⟩
  · exact (le_max_left d (max K 2)).trans (le_max_right E₁ _)
  · exact ((le_max_left K 2).trans (le_max_right d _)).trans (le_max_right E₁ _)
  · exact ((le_max_right K 2).trans (le_max_right d _)).trans (le_max_right E₁ _)
  · intro e he
    have he1 : E₁ ≤ e := (le_max_left E₁ _).trans he
    have he2 : 2 ≤ e := ((le_max_right K 2).trans (le_max_right d _)).trans ((le_max_right E₁ _).trans he)
    have heR : (0 : ℝ) < e := by exact_mod_cast (show 0 < e by omega)
    have hlog : 0 < Real.log (e : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < e by omega))
    have hp := hE₁ e he1
    change 0 < value d D γ r B K e / ((e : ℝ) ^ 3 * Real.log (e : ℝ)) -
      γ * ((weight d e : ℝ) / (e : ℝ) ^ 3) -
      Real.log ((size d e).factorial : ℝ) / ((e : ℝ) ^ 3 * Real.log (e : ℝ)) at hp
    have hmul := mul_pos hp (mul_pos (pow_pos heR 3) hlog)
    have heq : (value d D γ r B K e / ((e : ℝ) ^ 3 * Real.log (e : ℝ)) -
        γ * ((weight d e : ℝ) / (e : ℝ) ^ 3) -
        Real.log ((size d e).factorial : ℝ) / ((e : ℝ) ^ 3 * Real.log (e : ℝ))) *
          ((e : ℝ) ^ 3 * Real.log (e : ℝ)) =
        value d D γ r B K e - γ * (weight d e : ℝ) * Real.log (e : ℝ) -
          Real.log ((size d e).factorial : ℝ) := by field_simp [heR.ne', hlog.ne']
    rw [heq] at hmul
    linarith

end PaperP1.P3PrimeMassProxy
