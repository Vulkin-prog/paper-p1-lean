module

public import PaperP1.Model.GoodEdgePopulationBounds
public import PaperP1.Asymptotics.LogarithmicWordPowers
public import PaperP1.Asymptotics.CriticalWindowGeometry
public import PaperP1.Model.LocalRigidityConsequences

/-! # The independent good-edge product mass has the stronger rate one -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GoodEdgeAccidentalMass

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts

theorem uniform_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ H : ℝ, ∀ r : ℕ → ℝ,
      (∀ x ∈ dyadicBlock N, 0 ≤ r x ∧ r x ≤ (2 ^ L : ℝ)⁻¹) →
      (∑ e ∈ GoodEdgeCompression.goodEdges H N L, ∏ x ∈ e, r x) ≤
        (N : ℝ) ^ (-1 + ε) := by
  let K : ℝ := (2 : ℝ) ^ C
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NP, hp⟩ := LogarithmicWordPowers.polynomial_factor_le_rpow_eventually
    CriticalBandScale.upperScale CriticalBandScale.upperScale_pos.le (26 * K ^ 2) 1 ε hε
  refine ⟨3 + NG + NP, by omega, ?_⟩
  intro N hN L hband H r hr
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hwidth := (hg N (by omega) L hband).2.2.2.2.2
  have hcoef' : |(26 * K ^ 2) * ((L + 1 : ℕ) : ℝ)| ≤ (N : ℝ) ^ ε := by
    simpa only [Nat.cast_add, Nat.cast_one, pow_one] using hp N (by omega) L hwidth
  have hcoef : (26 * K ^ 2) * ((L + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ ε :=
    (le_abs_self _).trans hcoef'
  have hnom : (2 ^ L : ℝ)⁻¹ ≤ K / N :=
    LocalRigidityConsequences.nominal_marginal_bound (by omega) hband
  have hsquare := pow_le_pow_left₀ (by positivity : 0 ≤ (2 ^ L : ℝ)⁻¹) hnom 2
  calc
    _ ≤ (26 * (L + 1) * N : ℕ) * ((2 ^ L : ℝ)⁻¹) ^ 2 :=
      GoodEdgePopulationBounds.independent_mass_bound (by omega) H r _ hr
    _ ≤ (26 * (L + 1) * N : ℕ) * (K / N) ^ 2 :=
      mul_le_mul_of_nonneg_left hsquare (Nat.cast_nonneg _)
    _ = ((26 * K ^ 2) * ((L + 1 : ℕ) : ℝ)) * (N : ℝ) ^ (-1 : ℝ) := by
      rw [Real.rpow_neg_one]
      push_cast
      field_simp
    _ ≤ (N : ℝ) ^ ε * (N : ℝ) ^ (-1 : ℝ) :=
      mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hn.le _)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring

end PaperP1.GoodEdgeAccidentalMass
