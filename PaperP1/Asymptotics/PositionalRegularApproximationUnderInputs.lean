module

public import PaperP1.Asymptotics.PositionalBoundaryApproximationUnderInputs
public import PaperP1.Asymptotics.PositionalPairConversionRate
public import PaperP1.Asymptotics.RetainedIndependentDeficitRates

/-! # Four-fifths approximation of the actual full regular unsigned positional law

This norm estimate precedes restoration of excluded sites and polynomial
weights. Positivity of the original single rates is a separate obligation.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalRegularApproximationUnderInputs

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.CompletedPositionalLaw
  PaperP1.RetainedComponentActivityUnderInputs

theorem uniform_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : Parameters, Hypotheses p (min (ε / 16) (1 / 12)) →
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        let G := RegularStarts.regularStarts N L
        let E := GoodEdgeCompression.goodEdges (8 * (L + 1) : ℕ) N L
        ‖ofFinite (PositionalStoppedLaw.actualLaw G L) -
          PositionalCompoundPoisson.target G E (fun x ↦ infiniteMarginal x L) (infiniteJointMoment L)‖ ≤
          (N : ℝ) ^ (-4 / 5 + ε) := by
  obtain ⟨p, hp⟩ := PositionalBoundaryApproximationUnderInputs.uniform_bound C (ε / 2) (by positivity)
  obtain ⟨NC, _hNC, hc⟩ := PositionalPairConversionRate.uniform_bound C (ε / 2) (by positivity)
  obtain ⟨ND, _hND, hd⟩ := RetainedIndependentDeficitRates.uniform_strong C (ε / 2) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 4 (-4 / 5 + ε / 2) (ε / 2) (by positivity)
  refine ⟨p, ?_⟩
  intro hgeo
  have hscale : (ε / 2) / 8 = ε / 16 := by ring
  obtain ⟨NB, _hNB, hb⟩ := hp (by simpa only [hscale] using hgeo)
  refine ⟨10 + NC + ND + NG + NF + NB, by omega, ?_⟩
  intro N hN L hband
  dsimp only
  let G := RegularStarts.regularStarts N L
  let H : ℝ := (8 * (L + 1) : ℕ)
  let E := GoodEdgeCompression.goodEdges H N L
  let Q := PositionalStoppedLaw.actualReference G L (RetainedGoodEdges.Retained H N L)
  let R := ofFinite (PositionalRetainedReference.independent G L + PositionalRetainedReference.pairs G E L)
  let T := PositionalCompoundPoisson.target G E (fun x ↦ infiniteMarginal x L) (infiniteJointMoment L)
  let P := (N : ℝ) ^ (-4 / 5 + ε / 2)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hL : 0 < L := by have hh := hg N (by omega) L hband; omega
  have hB : ‖ofFinite (PositionalStoppedLaw.actualLaw G L) - ofFinite Q‖ ≤ P := by
    rw [← map_sub, norm_ofFinite]
    exact hb N (by omega) L hband
  have hD : ‖ofFinite Q - R‖ ≤ 2 * P := by
    rw [← map_sub, norm_ofFinite]
    have hh := PositionalRetainedReference.actual_norm_bound (N := N) (L := L) (by omega) hL H
    obtain ⟨hfirst, hsecond⟩ := hd N (by omega) L hband H
    have hfirstP := hfirst.trans (Real.rpow_le_rpow_of_exponent_le hn1
      (by linarith only [] : (-1 : ℝ) + ε / 2 ≤ -4 / 5 + ε / 2))
    have hsecondP := hsecond.trans (Real.rpow_le_rpow_of_exponent_le hn1
      (by linarith only [] : (-7 / 6 : ℝ) + ε / 2 ≤ -4 / 5 + ε / 2))
    change RetainedReferenceTheorem.firstMass N L ≤ P at hfirstP
    change RetainedReferenceTheorem.secondMass H N L ≤ P at hsecondP
    exact hh.trans (by linarith only [hfirstP, hsecondP])
  have hR : R = PositionalPairConversion.reference G E (fun x ↦ infiniteMarginal x L) (infiniteJointMoment L) := by
    dsimp only [R]
    rw [map_add, PositionalRetainedReference.independent_completed, PositionalRetainedReference.pairs_completed]
    simp only [PositionalPairConversion.reference]
    congr!
  have hC : ‖R - T‖ ≤ P := by
    rw [hR]
    exact (hc N (by omega) L hband H).trans (Real.rpow_le_rpow_of_exponent_le hn1
      (by linarith only [] : (-1 : ℝ) + ε / 2 ≤ -4 / 5 + ε / 2))
  have h1 := norm_add_le (ofFinite (PositionalStoppedLaw.actualLaw G L) - ofFinite Q) (ofFinite Q - R)
  rw [sub_add_sub_cancel] at h1
  have h2 := norm_add_le (ofFinite (PositionalStoppedLaw.actualLaw G L) - R) (R - T)
  rw [sub_add_sub_cancel] at h2
  have hfactor : 4 * P ≤ (N : ℝ) ^ (-4 / 5 + ε) := by
    convert hf N (by omega) using 1
    congr 1
    ring
  change ‖ofFinite (PositionalStoppedLaw.actualLaw G L) - T‖ ≤ _
  linarith only [hB, hD, hC, h1, h2, hfactor]

end PaperP1.PositionalRegularApproximationUnderInputs
