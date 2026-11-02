module

public import PaperP1.Model.PrincipalSecondMomentReduction
public import PaperP1.Asymptotics.AlignedPrincipalEdgePairMass
public import PaperP1.Asymptotics.SharedPrincipalEdgePairMass
public import PaperP1.Asymptotics.PrincipalEdgeSecondMomentLower

/-! # The only remaining actual principal-edge second-moment error is a literal residual covariance sum -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrincipalSecondMomentError

open Finset MeasureTheory PaperP1.PrincipalSecondMomentReduction PaperP1.PrincipalEdgeSpaces
  PaperP1.PrincipalChannelEdges PaperP1.Model.InfiniteRademacher

theorem uniform_error (J : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      |jointSecond N H L - beta N H L ^ 2| ≤ residualCovariance N H L J + (N : ℝ) ^ (-41 / 30 + ε) := by
  obtain ⟨NS, _hNS, hs⟩ := SharedPrincipalEdgePairMass.uniform_bound C (ε / 2) (by positivity)
  obtain ⟨NA, _hNA, ha⟩ := AlignedPrincipalEdgePairMass.uniform_bound J C (ε / 2) (by positivity)
  obtain ⟨NL, _hNL, hl⟩ := PrincipalEdgeSecondMomentLower.uniform_lower C (ε / 2) (by positivity)
  obtain ⟨NG, _hNG, hg⟩ := PrincipalChannelEdgesPhase.uniform_geometry C
  obtain ⟨NC, hc⟩ := HalfCountSchedule.factor_absorption 2 (-41 / 30 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 10 (max NS (max NA (max NL (max NG NC)))), by omega, ?_⟩
  intro N hN L H hband
  have hn₁ : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  obtain ⟨hL, hlarge⟩ := hg N (by omega) L hband
  have hfinite := finite_upper (H := H) (J := J) (by omega) hL hlarge
  have hshared := hs N (by omega) L H hband
  have haligned := ha N (by omega) L H hband
  have hlower := hl N (by omega) L H hband
  have hconst : 2 * (N : ℝ) ^ (-41 / 30 + ε / 2) ≤ (N : ℝ) ^ (-41 / 30 + ε) := by
    have hh := hc N (by omega)
    simpa only [show (-41 / 30 + ε / 2) + ε / 2 = -41 / 30 + ε by ring] using hh
  have hlowpow : (N : ℝ) ^ (-7 / 3 + ε / 2) ≤ (N : ℝ) ^ (-41 / 30 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hn₁ (by linarith only [hε])
  have hr := residual_nonneg N H L J
  exact abs_le.mpr ⟨by linarith only [hlower, hlowpow, hr], by linarith only [hfinite, hshared, haligned, hconst]⟩

theorem uniform_moment_error (J : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      |(∫ ω, (ActiveEdgeObservables.value (edges N H L) L ω ^ 2 - ActiveEdgeObservables.value (edges N H L) L ω)
        ∂infiniteRademacherMeasure) - beta N H L ^ 2| ≤
        residualCovariance N H L J + (N : ℝ) ^ (-41 / 30 + ε) := by
  obtain ⟨NE, _hNE, he⟩ := uniform_error J C ε hε
  obtain ⟨NG, _hNG, hg⟩ := PrincipalChannelEdgesPhase.uniform_geometry C
  refine ⟨max 10 (max NE NG), by omega, ?_⟩
  intro N hN L H hband
  rw [PrincipalEdgeSecondMomentLower.actual_second_eq (by omega) (hg N (by omega) L hband).2]
  exact he N (by omega) L H hband

theorem relative_error (J : ℕ) (C : ℝ) (D : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → 8 * (L + 1) ≤ H → H ≤ D * (L + 1) →
      |jointSecond N H L - beta N H L ^ 2| ≤ residualCovariance N H L J + δ * beta N H L ^ 2 := by
  obtain ⟨c, hc, NB, _hNB, hb⟩ := PrincipalEdgeProbability.beta_squared_lower C D
  obtain ⟨NE, _hNE, he⟩ := uniform_error J C (1 / 60) (by norm_num)
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
  exact herr.trans (add_le_add (le_refl _) herror)

theorem uniform_residual_lower (J : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      residualCovariance N H L J ≤ jointSecond N H L - beta N H L ^ 2 + (N : ℝ) ^ (-7 / 3 + ε) := by
  obtain ⟨NP, _hNP, hp⟩ := CoupledPrincipalProductMass.uniform_bound C (ε / 2) (by positivity)
  obtain ⟨NG, _hNG, hg⟩ := PrincipalChannelEdgesPhase.uniform_geometry C
  obtain ⟨NC, hc⟩ := HalfCountSchedule.factor_absorption 2 (-7 / 3 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 10 (max NP (max NG NC)), by omega, ?_⟩
  intro N hN L H hband
  obtain ⟨hL, hlarge⟩ := hg N (by omega) L hband
  have hfinite := finite_residual_lower (H := H) (J := J) (by omega) hL hlarge
  have hprod := hp N (by omega) L H hband
  have hconst : 2 * (N : ℝ) ^ (-7 / 3 + ε / 2) ≤ (N : ℝ) ^ (-7 / 3 + ε) := by
    simpa only [show (-7 / 3 + ε / 2) + ε / 2 = -7 / 3 + ε by ring] using hc N (by omega)
  linarith only [hfinite, hprod, hconst]

theorem uniform_error_comparison (J : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      |(|jointSecond N H L - beta N H L ^ 2|) - residualCovariance N H L J| ≤ (N : ℝ) ^ (-41 / 30 + ε) := by
  obtain ⟨NE, _hNE, he⟩ := uniform_error J C ε hε
  obtain ⟨NR, _hNR, hr⟩ := uniform_residual_lower J C ε hε
  refine ⟨max 10 (max NE NR), by omega, ?_⟩
  intro N hN L H hband
  have herr := he N (by omega) L H hband
  have hres := hr N (by omega) L H hband
  have hpow : (N : ℝ) ^ (-7 / 3 + ε) ≤ (N : ℝ) ^ (-41 / 30 + ε) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega)) (by linarith)
  have hself := le_abs_self (jointSecond N H L - beta N H L ^ 2)
  exact abs_le.mpr ⟨by linarith only [hres, hpow, hself], by linarith only [herr]⟩

theorem relative_error_comparison (J : ℕ) (C : ℝ) (D : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → 8 * (L + 1) ≤ H → H ≤ D * (L + 1) →
      |(|jointSecond N H L - beta N H L ^ 2|) - residualCovariance N H L J| ≤ δ * beta N H L ^ 2 := by
  obtain ⟨c, hc, NB, _hNB, hb⟩ := PrincipalEdgeProbability.beta_squared_lower C D
  obtain ⟨NE, _hNE, he⟩ := uniform_error_comparison J C (1 / 60) (by norm_num)
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

end PaperP1.PrincipalSecondMomentError
