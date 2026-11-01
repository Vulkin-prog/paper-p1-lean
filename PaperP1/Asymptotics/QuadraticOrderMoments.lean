module

public import PaperP1.Asymptotics.QuadraticOrderBranching
public import PaperP1.Model.FactorialBranching
public import PaperP1.Model.LocalRigidityConsequences
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Actual factorial moments through every fixed quadratic-logarithmic order -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.QuadraticOrderMoments

open Filter Finset PaperP1.Model PaperP1.FactorialCountMoments PaperP1.FactorialBranching
  PaperP1.BranchingExceptional PaperP1.OldValuePrimeBudget

theorem nominal_mean_bound {N L : ℕ} {C : ℝ} (hN : 2 ≤ N)
    (hband : |(L : ℝ) - Real.log N / Real.log 2| ≤ C) :
    (N : ℝ) * (2 ^ L : ℝ)⁻¹ ≤ (2 : ℝ) ^ C := by
  have h := mul_le_mul_of_nonneg_left (LocalRigidityConsequences.nominal_marginal_bound hN hband) (Nat.cast_nonneg N)
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  convert h using 1
  field_simp

theorem factorial_bound (C K ε : ℝ) (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ k : ℕ, (k : ℝ) ≤ K * (Real.log N) ^ 2 →
      factorialCountMoment (dyadicBlock N) L k ≤ (2 * (N : ℝ) ^ (3 / 4 + ε)) ^ k := by
  obtain ⟨Nbranch, hNbranch, hbranch⟩ := QuadraticOrderBranching.badStarts_card_critical C K ε hK hε
  obtain ⟨Nfinite, _, hfinite⟩ := ConditionalRankTheorem.finite_conditions C
  obtain ⟨Npow, hNpow⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop (by linarith : 0 < (3 / 4 : ℝ) + ε)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventually (eventually_ge_atTop ((2 : ℝ) ^ C)))
  refine ⟨max Nbranch (max Nfinite Npow), by omega, ?_⟩
  intro N hN L hband k horder
  obtain ⟨hN3, hLpos, _⟩ := hfinite N (by omega) L hband
  have hD : ∀ r < k, ∀ A : Finset ℕ, A ⊆ dyadicBlock N → A.card = r →
      ((badStarts N L (rawValues A L)).card : ℝ) ≤ (N : ℝ) ^ (3 / 4 + ε) := by
    intro r hr A hA hcard
    have horderR : (r : ℝ) ≤ K * (Real.log N) ^ 2 :=
      (show (r : ℝ) ≤ k by exact_mod_cast (Nat.le_of_lt hr)).trans horder
    exact hbranch N (by omega) r horderR L hband A hA hcard.le
  have hpow := factorial_le_power (by omega : 2 ≤ N) hLpos k ((N : ℝ) ^ (3 / 4 + ε))
    (Real.rpow_nonneg (Nat.cast_nonneg N) _) hD
  have hnom : (N : ℝ) * (2 ^ L : ℝ)⁻¹ ≤ (N : ℝ) ^ (3 / 4 + ε) :=
    (nominal_mean_bound (by omega) hband).trans (hNpow N (by omega))
  exact hpow.trans (pow_le_pow_left₀ (by positivity) (by linarith) k)

end PaperP1.QuadraticOrderMoments
