module

public import PaperP1.Diophantine.ZeroDegreeLinearFibres
public import PaperP1.Diophantine.ZeroDegreeQuadraticFibres
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Uniform polylogarithmic-shift budget for the degree-zero auxiliary case -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ZeroDegreeAuxiliaryCounts

open Filter

theorem polylog_shift_budget (k : ℕ) (C₀ C₁ A₀ : ℝ)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hA₀ : 0 ≤ A₀) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ h : ℤ, (h.natAbs : ℝ) ≤ (Real.log N) ^ A₀ →
      2 * (k + 1) * (C₀ * C₁ * h.natAbs + 1) ≤ (N : ℝ) ^ ε := by
  let K : ℝ := 2 * (k + 1) * (C₀ * C₁ + 1)
  have hK : 0 < K := by dsimp [K]; positivity
  have hlim := (isLittleO_log_rpow_rpow_atTop A₀ hε).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨Ns, hNs⟩ := eventually_atTop.mp (hlim.bound (one_div_pos.mpr hK))
  obtain ⟨Nl, hNl⟩ := eventually_atTop.mp
    ((Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually (eventually_ge_atTop 1))
  refine ⟨max 2 (max Ns Nl), ?_⟩
  intro N hN h hh
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 1 ≤ Real.log N := hNl N (by omega)
  have hp : 1 ≤ (Real.log N) ^ A₀ := Real.one_le_rpow hlog hA₀
  have hs := hNs N (by omega)
  have hs' : (Real.log N) ^ A₀ ≤ (1 / K) * (N : ℝ) ^ ε := by
    simpa only [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ Real.log N) _),
      abs_of_nonneg (Real.rpow_nonneg hn.le _)] using hs
  calc
    2 * (k + 1) * (C₀ * C₁ * h.natAbs + 1) ≤
        2 * (k + 1) * (C₀ * C₁ * (Real.log N) ^ A₀ + (Real.log N) ^ A₀) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add (mul_le_mul_of_nonneg_left hh (mul_nonneg hC₀ hC₁)) hp
    _ = K * (Real.log N) ^ A₀ := by dsimp [K]; ring
    _ ≤ K * ((1 / K) * (N : ℝ) ^ ε) := mul_le_mul_of_nonneg_left hs' hK.le
    _ = (N : ℝ) ^ ε := by field_simp

theorem linear_auxiliary_zero_count (k : ℕ) (C₀ C₁ A₀ : ℝ)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hA₀ : 0 ≤ A₀) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ c₁ c₂ : ℕ, 0 < c₁ → 0 < c₂ → ∀ h : ℤ, h ≠ 0 →
      (h.natAbs : ℝ) ≤ (Real.log N) ^ A₀ →
        ∀ F : MvPolynomial (Fin 2) ℤ, F.IsHomogeneous k → F ≠ 0 →
          ∀ S : Finset PaperP1.BidegreeOneFibreCount.Point,
            (∀ s ∈ S, PaperP1.ZeroDegreeLinearFibres.Valid c₁ c₂ h s) →
            (∀ s ∈ S, MvPolynomial.eval s.1 F = 0) →
            (∀ s ∈ S, (PaperP1.ZeroDegreeLinearFibres.coefficient₁ c₁ s.1 : ℝ) * s.2 1 ≤ C₁ * N) →
            (∀ s ∈ S, (N : ℝ) ≤ C₀ * (PaperP1.ZeroDegreeLinearFibres.coefficient₁ c₁ s.1 : ℝ) *
              PaperP1.ZeroDegreeLinearFibres.coefficient₂ c₂ s.1) →
                (S.card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨N₀, hN₀⟩ := polylog_shift_budget k C₀ C₁ A₀ hC₀ hC₁ hA₀ ε hε
  refine ⟨N₀, ?_⟩
  intro N hN c₁ c₂ hc₁ hc₂ h hh hshift F hF hF0 S hS hzero hheight hproduct
  exact (PaperP1.ZeroDegreeLinearFibres.auxiliary_zero_count k c₁ c₂ hc₁ hc₂ h hh N C₀ C₁
    (Nat.cast_nonneg N) hC₀ hC₁ F hF hF0 S hS hzero hheight hproduct).trans (hN₀ N hN h hshift)

end PaperP1.ZeroDegreeAuxiliaryCounts
