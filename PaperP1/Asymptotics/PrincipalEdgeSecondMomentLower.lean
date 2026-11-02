module

public import PaperP1.Asymptotics.CoupledPrincipalProductMass
public import PaperP1.Model.ActiveFamilySecondMoment

/-! # The complete ordered principal-edge second joint sum has its unconditional beta-squared lower bound -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrincipalEdgeSecondMomentLower

open Finset MeasureTheory PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteRademacher
  PaperP1.PrincipalEdgeSpaces PaperP1.PrincipalChannelEdges

theorem actual_second_eq {N H L : ℕ} (hN : 2 ≤ N) (hlarge : 29 * (L + 1) < N) :
    (∫ ω, (ActiveEdgeObservables.value (edges N H L) L ω ^ 2 - ActiveEdgeObservables.value (edges N H L) L ω)
      ∂infiniteRademacherMeasure) = jointSecond N H L := by
  have hsub := PrincipalChannelEdges.subset_pairs (H := H) hN hlarge
  exact ActiveFamilySecondMoment.infinite_mean_eq (M := dyadicCutoff N L) (edges N H L)
    (fun e he ↦ CountObservables.dyadic_subset_cutoff (mem_powersetCard.mp (hsub he)).1)

theorem uniform_lower (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      beta N H L ^ 2 - (N : ℝ) ^ (-7 / 3 + ε) ≤ jointSecond N H L := by
  obtain ⟨NM, _hNM, hm⟩ := CoupledPrincipalProductMass.uniform_bound C ε hε
  obtain ⟨NG, _hNG, hg⟩ := PrincipalChannelEdgesPhase.uniform_geometry C
  refine ⟨max 10 (max NM NG), by omega, ?_⟩
  intro N hN L H hband
  obtain ⟨hL, hlarge⟩ := hg N (by omega) L hband
  have hfinite := beta_squared_le_joint_add_coupled (H := H) (by omega) hL hlarge
  have hmass := hm N (by omega) L H hband
  linarith only [hfinite, hmass]

theorem relative_lower (C : ℝ) (D : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → 8 * (L + 1) ≤ H → H ≤ D * (L + 1) →
      (1 - δ) * beta N H L ^ 2 ≤ jointSecond N H L := by
  obtain ⟨c, hc, NB, _hNB, hb⟩ := PrincipalEdgeProbability.beta_squared_lower C D
  obtain ⟨NM, _hNM, hm⟩ := uniform_lower C (1 / 2) (by norm_num)
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption (1 / (δ * c)) (-11 / 6) (1 / 2) (by norm_num)
  refine ⟨max 10 (max NB (max NM NA)), by omega, ?_⟩
  intro N hN L H hband hcut hH
  have hbeta := hb N (by omega) L H hband hcut hH
  have hfactor : (N : ℝ) ^ (-11 / 6 : ℝ) / (δ * c) ≤ (N : ℝ) ^ (-4 / 3 : ℝ) := by
    have hh := ha N (by omega)
    rw [show (-11 / 6 : ℝ) + 1 / 2 = -4 / 3 by norm_num] at hh
    simpa only [div_eq_mul_inv, one_div, mul_comm, one_mul, mul_one] using hh
  have herror : (N : ℝ) ^ (-11 / 6 : ℝ) ≤ δ * beta N H L ^ 2 := by
    have hh := (div_le_iff₀ (by positivity : (0 : ℝ) < δ * c)).mp hfactor
    have hlow := mul_le_mul_of_nonneg_left hbeta hδ.le
    nlinarith only [hh, hlow]
  have hlower := hm N (by omega) L H hband
  rw [show (-7 / 3 : ℝ) + 1 / 2 = -11 / 6 by norm_num] at hlower
  nlinarith only [hlower, herror]

theorem uniform_moment_lower (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      beta N H L ^ 2 - (N : ℝ) ^ (-7 / 3 + ε) ≤
        ∫ ω, (ActiveEdgeObservables.value (edges N H L) L ω ^ 2 - ActiveEdgeObservables.value (edges N H L) L ω)
          ∂infiniteRademacherMeasure := by
  obtain ⟨NM, _hNM, hm⟩ := uniform_lower C ε hε
  obtain ⟨NG, _hNG, hg⟩ := PrincipalChannelEdgesPhase.uniform_geometry C
  refine ⟨max 10 (max NM NG), by omega, ?_⟩
  intro N hN L H hband
  rw [actual_second_eq (by omega) (hg N (by omega) L hband).2]
  exact hm N (by omega) L H hband

theorem relative_moment_lower (C : ℝ) (D : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → 8 * (L + 1) ≤ H → H ≤ D * (L + 1) →
      (1 - δ) * beta N H L ^ 2 ≤
        ∫ ω, (ActiveEdgeObservables.value (edges N H L) L ω ^ 2 - ActiveEdgeObservables.value (edges N H L) L ω)
          ∂infiniteRademacherMeasure := by
  obtain ⟨NM, _hNM, hm⟩ := relative_lower C D δ hδ
  obtain ⟨NG, _hNG, hg⟩ := PrincipalChannelEdgesPhase.uniform_geometry C
  refine ⟨max 10 (max NM NG), by omega, ?_⟩
  intro N hN L H hband hcut hH
  rw [actual_second_eq (by omega) (hg N (by omega) L hband).2]
  exact hm N (by omega) L H hband hcut hH

end PaperP1.PrincipalEdgeSecondMomentLower
