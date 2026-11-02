module

public import PaperP1.Model.PrincipalResidualDensity
public import PaperP1.Asymptotics.CriticalBinaryGrowth
public import PaperP1.Asymptotics.PrincipalSecondMomentReduction

/-! # Only residual block intersections exceeding 29L/30 can affect the principal-edge second-moment scale -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrincipalDenseResidual

open Finset MeasureTheory PaperP1.PrincipalResidualDensity PaperP1.JointBlockCovariance
  PaperP1.PrincipalEdgeSpaces PaperP1.PrincipalChannelEdges PaperP1.PrincipalSecondMomentReduction
  PaperP1.Model.InfiniteRademacher

theorem bounded_mass (θ C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      boundedCovariance N H L θ ≤ (N : ℝ) ^ (-7 / 3 + θ + ε) := by
  obtain ⟨NP, _hNP, hp⟩ := CoupledPrincipalProductMass.uniform_bound C (ε / 2) (by positivity)
  obtain ⟨NR, _hNR, hr⟩ := CriticalBinaryGrowth.uniform_upper C θ (ε / 2) (by positivity)
  obtain ⟨NG, _hNG, hg⟩ := PrincipalChannelEdgesPhase.uniform_geometry C
  refine ⟨max 10 (max NP (max NR NG)), by omega, ?_⟩
  intro N hN L H hband
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hfinite := bounded_by_cap (N := N) (H := H) (θ := θ) (hg N (by omega) L hband).1
    (Real.rpow_nonneg hn.le (θ + ε / 2)) (by
      intro p hp'
      exact hr N (by omega) L (intersectionRank L p.1 p.2) hband (mem_filter.mp hp').2)
  calc
    _ ≤ (N : ℝ) ^ (θ + ε / 2) * coupledProductMass N H L := hfinite
    _ ≤ (N : ℝ) ^ (θ + ε / 2) * (N : ℝ) ^ (-7 / 3 + ε / 2) :=
      mul_le_mul_of_nonneg_left (hp N (by omega) L H hband) (Real.rpow_nonneg hn.le _)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring

theorem uniform_dense_comparison (J : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      |(|jointSecond N H L - beta N H L ^ 2|) - denseCovariance N H L J (29 / 30)| ≤
        (N : ℝ) ^ (-41 / 30 + ε) := by
  obtain ⟨NE, _hNE, he⟩ := PrincipalSecondMomentError.uniform_error_comparison J C (ε / 2) (by positivity)
  obtain ⟨NB, _hNB, hb⟩ := bounded_mass (29 / 30) C (ε / 2) (by positivity)
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption 2 (-41 / 30 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 10 (max NE (max NB NA)), by omega, ?_⟩
  intro N hN L H hband
  have herr := he N (by omega) L H hband
  have hbounded := hb N (by omega) L H hband
  rw [show (-7 / 3 : ℝ) + 29 / 30 + ε / 2 = -41 / 30 + ε / 2 by ring] at hbounded
  have hgap : |residualCovariance N H L J - denseCovariance N H L J (29 / 30)| ≤
      boundedCovariance N H L (29 / 30) := by
    rw [abs_of_nonneg (sub_nonneg.mpr (dense_le_residual N H L J (29 / 30)))]
    have hh := residual_le_bounded_add_dense N H L J (29 / 30)
    linarith only [hh]
  calc
    _ = |((|jointSecond N H L - beta N H L ^ 2|) - residualCovariance N H L J) +
        (residualCovariance N H L J - denseCovariance N H L J (29 / 30))| := by congr 1; ring
    _ ≤ |(|jointSecond N H L - beta N H L ^ 2|) - residualCovariance N H L J| +
        |residualCovariance N H L J - denseCovariance N H L J (29 / 30)| := abs_add_le _ _
    _ ≤ (N : ℝ) ^ (-41 / 30 + ε / 2) + boundedCovariance N H L (29 / 30) := add_le_add herr hgap
    _ ≤ 2 * (N : ℝ) ^ (-41 / 30 + ε / 2) := by linarith only [hbounded]
    _ ≤ (N : ℝ) ^ ((-41 / 30 + ε / 2) + ε / 2) := ha N (by omega)
    _ = _ := by congr 1; ring

theorem uniform_dense_lower (J : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      denseCovariance N H L J (29 / 30) ≤ jointSecond N H L - beta N H L ^ 2 + (N : ℝ) ^ (-7 / 3 + ε) := by
  obtain ⟨NR, hNR, hr⟩ := PrincipalSecondMomentError.uniform_residual_lower J C ε hε
  exact ⟨NR, hNR, fun N hN L H hband ↦ (dense_le_residual N H L J (29 / 30)).trans (hr N hN L H hband)⟩

theorem relative_dense_comparison (J : ℕ) (C : ℝ) (D : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → 8 * (L + 1) ≤ H → H ≤ D * (L + 1) →
      |(|jointSecond N H L - beta N H L ^ 2|) - denseCovariance N H L J (29 / 30)| ≤ δ * beta N H L ^ 2 := by
  obtain ⟨c, hc, NB, _hNB, hb⟩ := PrincipalEdgeProbability.beta_squared_lower C D
  obtain ⟨NE, _hNE, he⟩ := uniform_dense_comparison J C (1 / 60) (by norm_num)
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption (1 / (δ * c)) (-27 / 20) (1 / 60) (by norm_num)
  refine ⟨max 10 (max NB (max NE NA)), by omega, ?_⟩
  intro N hN L H hband hcut hH
  have hbeta := hb N (by omega) L H hband hcut hH
  have hfactor : (N : ℝ) ^ (-27 / 20 : ℝ) / (δ * c) ≤ (N : ℝ) ^ (-4 / 3 : ℝ) := by
    have hh := ha N (by omega)
    rw [show (-27 / 20 : ℝ) + 1 / 60 = -4 / 3 by norm_num] at hh
    simpa only [div_eq_mul_inv, one_div, mul_comm, one_mul, mul_one] using hh
  have herror : (N : ℝ) ^ (-27 / 20 : ℝ) ≤ δ * beta N H L ^ 2 := by
    have hh := (div_le_iff₀ (by positivity : (0 : ℝ) < δ * c)).mp hfactor
    have hlow := mul_le_mul_of_nonneg_left hbeta hδ.le
    nlinarith only [hh, hlow]
  have herr := he N (by omega) L H hband
  rw [show (-41 / 30 : ℝ) + 1 / 60 = -27 / 20 by norm_num] at herr
  exact herr.trans herror

theorem uniform_dense_moment_comparison (J : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      |(|(∫ ω, (ActiveEdgeObservables.value (edges N H L) L ω ^ 2 - ActiveEdgeObservables.value (edges N H L) L ω)
        ∂infiniteRademacherMeasure) - beta N H L ^ 2|) - denseCovariance N H L J (29 / 30)| ≤
        (N : ℝ) ^ (-41 / 30 + ε) := by
  obtain ⟨NE, _hNE, he⟩ := uniform_dense_comparison J C ε hε
  obtain ⟨NG, _hNG, hg⟩ := PrincipalChannelEdgesPhase.uniform_geometry C
  refine ⟨max 10 (max NE NG), by omega, ?_⟩
  intro N hN L H hband
  rw [PrincipalEdgeSecondMomentLower.actual_second_eq (by omega) (hg N (by omega) L hband).2]
  exact he N (by omega) L H hband

end PaperP1.PrincipalDenseResidual
