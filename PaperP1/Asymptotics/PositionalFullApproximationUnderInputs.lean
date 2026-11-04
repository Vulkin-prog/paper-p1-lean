module

public import PaperP1.Asymptotics.PositionalRegularApproximationUnderInputs
public import PaperP1.Asymptotics.PositionalRestorationRates

/-! # The full original unsigned field has the source unweighted four-fifths rate

The polynomially weighted assertion of main 20.1 remains separate.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalFullApproximationUnderInputs

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.CompletedPositionalLaw
  PaperP1.RetainedComponentActivityUnderInputs

theorem uniform_norm_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : Parameters, Hypotheses p (min (ε / 32) (1 / 12)) →
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        ‖ofFinite (PositionalStoppedLaw.actualLaw (dyadicBlock N) L) -
          PositionalCompoundPoisson.target (dyadicBlock N) (GoodEdgeCompression.goodEdges (8 * (L + 1) : ℕ) N L)
            (fun _ ↦ (2 ^ L : ℝ)⁻¹) (infiniteJointMoment L)‖ ≤ (N : ℝ) ^ (-4 / 5 + ε) := by
  obtain ⟨p, hp⟩ := PositionalRegularApproximationUnderInputs.uniform_bound C (ε / 2) (by positivity)
  obtain ⟨NA, _hNA, ha⟩ := PositionalRestorationRates.uniform_actual_bound C (ε / 2) (by positivity)
  obtain ⟨NT, _hNT, ht⟩ := PositionalRestorationRates.uniform_target_bound C (ε / 2) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 3 (-4 / 5 + ε / 2) (ε / 2) (by positivity)
  refine ⟨p, ?_⟩
  intro hgeo
  have hscale : (ε / 2) / 16 = ε / 32 := by ring
  obtain ⟨NR, _hNR, hr⟩ := hp (by simpa only [hscale] using hgeo)
  refine ⟨10 + NA + NT + NG + NF + NR, by omega, ?_⟩
  intro N hN L hband
  let G := RegularStarts.regularStarts N L
  let E := GoodEdgeCompression.goodEdges (8 * (L + 1) : ℕ) N L
  let A := ofFinite (PositionalStoppedLaw.actualLaw (dyadicBlock N) L)
  let B := ofFinite (PositionalStoppedLaw.actualLaw G L)
  let T := PositionalCompoundPoisson.target (dyadicBlock N) E (fun _ ↦ (2 ^ L : ℝ)⁻¹) (infiniteJointMoment L)
  let R := PositionalCompoundPoisson.target G E (fun _ ↦ (2 ^ L : ℝ)⁻¹) (infiniteJointMoment L)
  let P := (N : ℝ) ^ (-4 / 5 + ε / 2)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hL : 0 < L := by have hh := hg N (by omega) L hband; omega
  have hAP : ‖A - B‖ ≤ P := (ha N (by omega) L hband).trans (Real.rpow_le_rpow_of_exponent_le hn1
    (by linarith only [] : (-1 : ℝ) + ε / 2 ≤ -4 / 5 + ε / 2))
  have hRP : ‖R - T‖ ≤ P := by
    rw [norm_sub_rev]
    exact (ht N (by omega) L hband (8 * (L + 1) : ℕ)).trans (Real.rpow_le_rpow_of_exponent_le hn1
      (by linarith only [] : (-1 : ℝ) + ε / 2 ≤ -4 / 5 + ε / 2))
  have hBR : ‖B - R‖ ≤ P := by
    have hh := hr N (by omega) L hband
    have he : PositionalCompoundPoisson.target G E (fun x ↦ infiniteMarginal x L) (infiniteJointMoment L) = R :=
      PositionalTargetExtension.target_congr G E _ _ _
        (fun x hx ↦ RetainedReferenceTheorem.ground_marginal (by omega) hL x hx)
    change ‖B - PositionalCompoundPoisson.target G E (fun x ↦ infiniteMarginal x L) (infiniteJointMoment L)‖ ≤ P at hh
    rwa [he] at hh
  have h1 := norm_add_le (A - B) (B - R)
  rw [sub_add_sub_cancel] at h1
  have h2 := norm_add_le (A - R) (R - T)
  rw [sub_add_sub_cancel] at h2
  have hfactor : 3 * P ≤ (N : ℝ) ^ (-4 / 5 + ε) := by
    convert hf N (by omega) using 1
    congr 1
    ring
  change ‖A - T‖ ≤ _
  linarith only [hAP, hBR, hRP, h1, h2, hfactor]

theorem uniform_probability_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : Parameters, Hypotheses p (min (ε / 32) (1 / 12)) →
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        let T := PositionalCompoundPoisson.target (dyadicBlock N) (GoodEdgeCompression.goodEdges (8 * (L + 1) : ℕ) N L)
          (fun _ ↦ (2 ^ L : ℝ)⁻¹) (infiniteJointMoment L)
        PositivePositionalConvolution.IsProbability T ∧
        (∑' v : PositionalFiniteLaw.Configuration ℕ,
          |Model.InfiniteRademacher.infiniteRademacherMeasure.real
              {ω | PositionalFiniteLaw.configuration (dyadicBlock N) (fun x ↦ infiniteStartIndicator x L) ω = v} -
            coeff v T|) ≤ (N : ℝ) ^ (-4 / 5 + ε) := by
  obtain ⟨p, hp⟩ := uniform_norm_bound C ε hε
  obtain ⟨NP, _hNP, hprob⟩ := WeakPairIncidence.full_target_isProbability C
  refine ⟨p, ?_⟩
  intro hgeo
  obtain ⟨NN, _hNN, hh⟩ := hp hgeo
  refine ⟨10 + NP + NN, by omega, ?_⟩
  intro N hN L hband
  dsimp only
  refine ⟨hprob N (by omega) L hband (8 * (L + 1) : ℕ), ?_⟩
  have hm := hh N (by omega) L hband
  rw [PositionalCoefficientExpansion.norm_eq_tsum_abs_coeff] at hm
  simpa only [map_sub, coeff_ofFinite, PositionalStoppedLaw.actualLaw_coeff] using hm

end PaperP1.PositionalFullApproximationUnderInputs
