module

public import PaperP1.Model.HomogeneousEffectiveWeights
public import PaperP1.Asymptotics.CriticalWindowGeometry

/-! # Uniform homogeneous single-window probabilities, including incompatible irregular windows -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousLocalMarginalCap

open Finset PaperP1.Arithmetic PaperP1.Model

theorem uniform_cap (C : ℝ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ x ∈ dyadicBlock N,
      HomogeneousRunMass.probability L {x} ≤ 2 * (2 : ℝ) ^ C / N := by
  obtain ⟨NR, hr⟩ := LocalRigidityRegimes.critical_band_relation_rank_le_one (1 / 2) C (by norm_num)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨max 2 (max NR NG), by omega, ?_⟩
  intro N hN L hband x hx
  have hgeom := hg N (by omega) L hband
  have hL : 0 < L := by omega
  have hxpos : 0 < x := by have hh := (mem_Ico.mp hx).1; omega
  have hbase : (1 / 2 : ℝ) * N ≤ ((x - 1 : ℕ) : ℝ) := by
    have hh : N ≤ 2 * (x - 1) := by have h := (mem_Ico.mp hx).1; omega
    have hR : (N : ℝ) ≤ 2 * (x - 1 : ℕ) := by exact_mod_cast hh
    linarith only [hR]
  have hrel := hr N (by omega) (x - 1) L hbase hband
  have hlocal : HomogeneousRunMass.probability L {x} ≤ 2 * (2 ^ L : ℝ)⁻¹ := by
    rw [HomogeneousEffectiveWeights.singleton_rank]
    rcases LocalRigidityConsequences.effective_rank_eq_or_pred hxpos hrel with h | h
    · rw [h]
      have hp : 0 ≤ (2 ^ L : ℝ)⁻¹ := by positivity
      linarith only [hp]
    · rw [h, LocalRigidityConsequences.inverse_two_pow_pred hL]
  exact hlocal.trans (by
    have hh := mul_le_mul_of_nonneg_left
      (LocalRigidityConsequences.nominal_marginal_bound (by omega) hband) (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [mul_div_assoc] using hh)

end PaperP1.HomogeneousLocalMarginalCap
