module

public import PaperP1.Asymptotics.OriginalPairHosts
public import PaperP1.Asymptotics.OriginalWindowFamilyMass
public import PaperP1.Model.PairHostMoment

/-! # The original second factorial moment is uniformly subpolynomial

This is a proved bound N^epsilon for every fixed epsilon, rather than the
bounded pair seed still needed in the recorded T19.4 source proof.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SecondMomentSubpower

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.FactorialCountMoments

theorem uniform_subpower (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      factorialCountMoment (dyadicBlock N) L 2 ≤ (N : ℝ) ^ ε := by
  let η := ε / 2
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨NH, hNHtwo, hNH⟩ := OriginalPairHosts.uniform_count C η hη
  obtain ⟨K, hK, NM, hNM⟩ := OriginalWindowFamilyMass.uniform_marginals C
  obtain ⟨NG, hNG⟩ := CriticalWindowGeometry.uniform_geometry C 0
  obtain ⟨NF, hNF⟩ := HalfCountSchedule.factor_absorption (((2 : ℝ) ^ C) ^ 2 + K) η η hη
  refine ⟨max NH (max NM (max NG NF)), ?_⟩
  intro N hN L hband
  have hNtwo : 2 ≤ N := by omega
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hcap := fun x hx ↦ (hNM N (by omega) L x hband hx).2
  have hL : 0 < L := by have h := (hNG N (by omega) L hband).2.2.1; omega
  have hfinite := PairHostMoment.finite_second_bound hNtwo hL (div_nonneg hK.le hn.le) hcap
  have hhosts := hNH N (by omega) L hband
  have hnom := LocalRigidityConsequences.nominal_marginal_bound hNtwo hband
  have hnp : (N : ℝ) * (2 ^ L : ℝ)⁻¹ ≤ (2 : ℝ) ^ C := by
    simpa only [mul_comm] using (le_div_iff₀ hn).mp hnom
  have hsquare : (N : ℝ) ^ 2 * ((2 ^ L : ℝ)⁻¹) ^ 2 ≤ ((2 : ℝ) ^ C) ^ 2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (by positivity : 0 ≤ (N : ℝ) * (2 ^ L : ℝ)⁻¹) hnp 2
  have hproduct : (N : ℝ) ^ (1 + η) * (K / N) = K * (N : ℝ) ^ η := by
    rw [Real.rpow_add hn, Real.rpow_one]
    field_simp
  have hhostMass : ((PairHostCover.hosts N L).card : ℝ) * (K / N) ≤ K * (N : ℝ) ^ η := by
    rw [← hproduct]
    exact mul_le_mul_of_nonneg_right hhosts (div_nonneg hK.le hn.le)
  have hpower := Real.one_le_rpow hn1 hη.le
  calc
    _ ≤ ((2 : ℝ) ^ C) ^ 2 + K * (N : ℝ) ^ η := hfinite.trans (add_le_add hsquare hhostMass)
    _ ≤ (((2 : ℝ) ^ C) ^ 2 + K) * (N : ℝ) ^ η := by
      have h := mul_le_mul_of_nonneg_left hpower (sq_nonneg ((2 : ℝ) ^ C))
      nlinarith only [h]
    _ ≤ (N : ℝ) ^ (η + η) := hNF N (by omega)
    _ = _ := by congr 1; dsimp [η]; ring

end PaperP1.SecondMomentSubpower
