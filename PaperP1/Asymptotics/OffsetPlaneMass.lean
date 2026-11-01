module

public import PaperP1.Arithmetic.OffsetPlaneMass
public import PaperP1.Asymptotics.SaturationDegrees
public import PaperP1.Model.LocalRigidityConsequences

/-! # The two-plane mass bound uniformly over the critical band -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OffsetPlaneMassAsymptotic

open PaperP1.OffsetPlaneMass PaperP1.CriticalBandScale PaperP1.LogarithmicWordPowers

theorem critical_finite_bound {N L : ℕ} {C : ℝ} (hN : 2 ≤ N) (hL : 0 < L)
    (hband : |(L : ℝ) - Real.log N / Real.log 2| ≤ C) :
    pairMass N L ≤ ((2 : ℝ) ^ C) ^ 2 * ((L + 1 : ℕ) : ℝ) ^ 18 / N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hnom := PaperP1.LocalRigidityConsequences.nominal_marginal_bound hN hband
  calc
    _ ≤ ((L + 1 : ℕ) : ℝ) ^ 18 * N * ((2 ^ L : ℝ)⁻¹) ^ 2 := pairMass_bound hN hL
    _ ≤ ((L + 1 : ℕ) : ℝ) ^ 18 * N * (((2 : ℝ) ^ C) / N) ^ 2 := by
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hnom 2) (by positivity)
    _ = _ := by field_simp

/-- The third start need not be regular or direct from either of the first two. -/
theorem pairMass_le_power_eventually (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → pairMass N L ≤ (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨Nfinite, hfinite⟩ := PaperP1.SaturationDegrees.finite_conditions C 2 (by norm_num)
  obtain ⟨Npoly, hpoly⟩ := polynomial_factor_le_rpow_eventually upperScale upperScale_pos.le
    (((2 : ℝ) ^ C) ^ 2) 18 ε hε
  refine ⟨max Nfinite Npoly, ?_⟩
  intro N hN L hL
  obtain ⟨hN10, hB, _, _, hwidth⟩ := hfinite N (by omega) L hL
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hcoef : ((2 : ℝ) ^ C) ^ 2 * ((L + 1 : ℕ) : ℝ) ^ 18 ≤ (N : ℝ) ^ ε := by
    have h := hpoly N (by omega) L hwidth
    simpa only [Nat.cast_add, Nat.cast_one, abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ ((2 : ℝ) ^ C) ^ 2 * (L + 1 : ℝ) ^ 18)] using h
  calc
    _ ≤ ((2 : ℝ) ^ C) ^ 2 * ((L + 1 : ℕ) : ℝ) ^ 18 / N := critical_finite_bound (by omega) (by omega) hL
    _ ≤ (N : ℝ) ^ ε / N := div_le_div_of_nonneg_right hcoef hn.le
    _ = _ := by rw [show -1 + ε = ε - 1 by ring, Real.rpow_sub hn, Real.rpow_one]

theorem primitiveMass_le_power_eventually (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → primitiveMass N L ≤ (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨N₀, hN₀⟩ := pairMass_le_power_eventually C ε hε
  exact ⟨N₀, fun N hN L hL ↦ (primitiveMass_le_pairMass N L).trans (hN₀ N hN L hL)⟩

end PaperP1.OffsetPlaneMassAsymptotic
