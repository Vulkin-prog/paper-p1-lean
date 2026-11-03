module

public import PaperP1.Asymptotics.FixedHeightQuadraticLawUnderInputs
public import PaperP1.Asymptotics.ExplicitHermiteComparison

/-! # Every fixed-height Hermite approximation has the same actual-law rate and moving equivalent -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ExplicitHermiteLawUnderInputs

open Finset MeasureTheory PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.FiniteChannelHierarchy PaperP1.ChannelMassPhaseEquivalent
  PaperP1.FixedHeightQuadraticLawUnderInputs

theorem uniform_bound (h : ℕ) (hh : 3 ≤ h) (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : Parameters, Hypotheses p (ε / 2) →
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      SignedAtomicDistance.distance (RetainedModifiedLaw.originalLaw (dyadicBlock N) L : Measure ℕ).toSignedMeasure
        (CompletedLaw.toSignedMeasure (HermiteReference.reference (nominalMean N L) (coefficient N L h))) ≤
          (N : ℝ) ^ (-1 + 1 / ((h + 1 : ℕ) : ℝ) + ε) := by
  obtain ⟨p, hp⟩ := uniform_coarse h hh C (ε / 2) (by positivity)
  obtain ⟨NE, _hNE, he⟩ := ExplicitHermiteComparison.uniform_bound C h hh (ε / 2) (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2
    (-1 + 1 / ((h + 1 : ℕ) : ℝ) + ε / 2) (ε / 2) (by positivity)
  refine ⟨p, ?_⟩
  intro hgeo
  obtain ⟨NP, _hNP, hp⟩ := hp hgeo
  refine ⟨max 2 (max NP (max NE NF)), by omega, ?_⟩
  intro N hN L hband
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hi : (0 : ℝ) ≤ 1 / ((h + 1 : ℕ) : ℝ) := by positivity
  have herror : ExplicitHermiteComparison.signedError N L h ≤
      (N : ℝ) ^ (-1 + 1 / ((h + 1 : ℕ) : ℝ) + ε / 2) :=
    (he N (by omega) L hband).trans (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hi]))
  have htriangle := SignedAtomicDistance.triangle
    (RetainedModifiedLaw.originalLaw (dyadicBlock N) L : Measure ℕ).toSignedMeasure
    (QuadraticPoisson.reference (nominalMean N L) (coefficient N L h))
    (CompletedLaw.toSignedMeasure (HermiteReference.reference (nominalMean N L) (coefficient N L h)))
  have heq : SignedAtomicDistance.distance
      (QuadraticPoisson.reference (nominalMean N L) (coefficient N L h))
      (CompletedLaw.toSignedMeasure (HermiteReference.reference (nominalMean N L) (coefficient N L h))) =
      ExplicitHermiteComparison.signedError N L h := by
    unfold SignedAtomicDistance.distance ExplicitHermiteComparison.signedError
    simp only [_root_.sub_apply]
  rw [heq] at htriangle
  have hquad := hp N (by omega) L hband
  calc
    _ ≤ 2 * (N : ℝ) ^ (-1 + 1 / ((h + 1 : ℕ) : ℝ) + ε / 2) := by linarith only [htriangle, herror, hquad]
    _ ≤ (N : ℝ) ^ ((-1 + 1 / ((h + 1 : ℕ) : ℝ) + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

theorem uniform_probability_equivalent (h : ℕ) (hh : 3 ≤ h) (C : ℝ) :
    ∃ p : Parameters, Hypotheses p (phaseMargin h) → ∀ τ : ℝ, 0 < τ →
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∃ H : ProbabilityMeasure ℕ,
        (H : Measure ℕ).toSignedMeasure = CompletedLaw.toSignedMeasure
          (HermiteReference.reference (nominalMean N L) (coefficient N L h)) ∧
        0 < AdjacentReferencePhase.leadingGap N L h ∧
        |AtomicProbability.totalVariation (RetainedModifiedLaw.originalLaw (dyadicBlock N) L) H /
          (phaseMass N L (h + 1) * PoissonDifferenceSigned.norm (nominalMean N L) 2 / 4) - 1| ≤ τ := by
  obtain ⟨p, hp⟩ := FixedHeightQuadraticLawUnderInputs.uniform_relative h hh C
  obtain ⟨NE, _hNE, he⟩ := ExplicitHermiteComparison.uniform_bound C h hh (1 / 12) (by norm_num)
  obtain ⟨NH, _hNH, hh₀⟩ := ExplicitReferenceAdmissibility.uniform_probabilities C h hh
  refine ⟨p, ?_⟩
  intro hgeo τ hτ
  obtain ⟨NQ, _hNQ, hq⟩ := hp hgeo (τ / 2) (by positivity)
  obtain ⟨NP, _hNP, hpower⟩ := power_negligible h hh C (τ / 2) (by positivity)
  refine ⟨max 2 (max NE (max NH (max NQ NP))), by omega, ?_⟩
  intro N hN L hband
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  obtain ⟨H, hH⟩ := (hh₀ N (by omega) L hband).2.2.2
  obtain ⟨hpos, hrelative⟩ := hq N (by omega) L hband
  have herror := he N (by omega) L hband
  rw [show (-4 / 3 : ℝ) + 1 / 12 = -5 / 4 by ring] at herror
  have hi : (0 : ℝ) ≤ 1 / ((h + 2 : ℕ) : ℝ) := by positivity
  have hsmall : ExplicitHermiteComparison.signedError N L h ≤ (τ / 2) * AdjacentReferencePhase.leadingGap N L h :=
    (herror.trans (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hi, (phaseMargin_pos h)]))).trans
      (hpower N (by omega) L hband)
  let P := (RetainedModifiedLaw.originalLaw (dyadicBlock N) L : Measure ℕ).toSignedMeasure
  let Q := QuadraticPoisson.reference (nominalMean N L) (coefficient N L h)
  let S := CompletedLaw.toSignedMeasure (HermiteReference.reference (nominalMean N L) (coefficient N L h))
  have hstable := distance_stability S Q P
  rw [distance_symm S P, distance_symm Q P, distance_symm S Q] at hstable
  have heq : SignedAtomicDistance.distance Q S = ExplicitHermiteComparison.signedError N L h := by
    unfold SignedAtomicDistance.distance ExplicitHermiteComparison.signedError
    simp only [_root_.sub_apply, Q, S]
  rw [heq] at hstable
  have htriangle := abs_sub_le (SignedAtomicDistance.distance P S) (SignedAtomicDistance.distance P Q)
    (AdjacentReferencePhase.leadingGap N L h)
  have hall : |SignedAtomicDistance.distance P S - AdjacentReferencePhase.leadingGap N L h| ≤
      τ * AdjacentReferencePhase.leadingGap N L h := by linarith only [hstable, htriangle, hsmall, hrelative]
  have hratio := PrincipalPairPhaseComparison.ratio_bound hpos hall
  have hdist := SignedAtomicDistance.probability_eq (RetainedModifiedLaw.originalLaw (dyadicBlock N) L) H
  rw [hH] at hdist
  change SignedAtomicDistance.distance P S = _ at hdist
  rw [hdist] at hratio
  refine ⟨H, hH, hpos, ?_⟩
  convert hratio using 1
  congr 2
  unfold AdjacentReferencePhase.leadingGap
  field_simp
  ring

end PaperP1.ExplicitHermiteLawUnderInputs
