module

public import PaperP1.Asymptotics.PositiveBoundaryMass
public import PaperP1.Asymptotics.LargeBoundaryTail
public import PaperP1.Asymptotics.BoundaryCutoffTrial
public import PaperP1.Model.RetainedStoppedLaw

/-! # The actual regular count law is approximated by the retained binomial pair reference at rate four-fifths -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RetainedBinomialApproximation

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.RetainedReferenceTheorem
  PaperP1.RetainedComponentActivity

theorem uniform_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        SignedAtomicDistance.distance
          (RetainedModifiedLaw.originalLaw (RegularStarts.regularStarts N L) L : MeasureTheory.Measure ℕ).toSignedMeasure
          (FiniteLawEmbedding.embed (binomialReference (8 * (L + 1) : ℕ) N L)) ≤ (N : ℝ) ^ (-4 / 5 + ε) := by
  obtain ⟨NP, _hNP, hp⟩ := PositiveBoundaryMass.uniform_bound C (ε / 2) (by positivity)
  let Λ : ℝ := (2 : ℝ) ^ C
  have hΛ : 0 < Λ := Real.rpow_pos_of_pos (by norm_num) C
  obtain ⟨NQ, hq⟩ := BoundaryCutoffTrial.critical_quarter_range C Λ hΛ
  obtain ⟨NL, hl⟩ := LargeBoundaryTail.improved_source_tail C
  obtain ⟨NG, hg⟩ := LargeBoundaryTail.critical_parameters C
  obtain ⟨ND, _hND, hd⟩ := RetainedIndependentDeficitRates.uniform_strong C (ε / 2) (by positivity)
  let A : ℝ := 3 + 2 * (2 : ℝ) ^ (4 * C / 3)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption A (-4 / 5 + ε / 2) (ε / 2) (by positivity)
  refine ⟨10 + NQ + NL + NG + ND + NF + NP, by omega, ?_⟩
  intro N hN L hband
  have hgeom := hg N (by omega) L hband
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  let K := BoundaryCutoff.cutoff Λ hΛ N
  let H : ℝ := (8 * (L + 1) : ℕ)
  let P := (N : ℝ) ^ (-4 / 5 + ε / 2)
  have hquarter := hq N (by omega) L hband
  have hK : 4 * K ≤ L := by dsimp only [K]; omega
  have hsmall := hp N (by omega) L hband K hK
  change RetainedBoundaryPositiveMass.mass H N L K ≤ P at hsmall
  have hlarge : LargeBoundaryMass.mass H N L K ≤ (2 * (2 : ℝ) ^ (4 * C / 3)) * P := by
    apply (hl N (by omega) L hband H).trans
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hε])) (by positivity)
  obtain ⟨hfirst, hsecond⟩ := hd N (by omega) L hband H
  have hfirstP : firstMass N L ≤ P := hfirst.trans (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only []))
  have hsecondP : secondMass H N L ≤ P := hsecond.trans (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only []))
  have hfinite := RetainedStoppedLaw.binomial_bound H N L K hgeom.1 hgeom.2
  have hbudget : SignedAtomicDistance.distance
      (RetainedModifiedLaw.originalLaw (RegularStarts.regularStarts N L) L : MeasureTheory.Measure ℕ).toSignedMeasure
      (FiniteLawEmbedding.embed (binomialReference H N L)) ≤ A * P := by
    dsimp only [A]
    linarith only [hfinite, hsmall, hlarge, hfirstP, hsecondP]
  calc
    _ ≤ A * P := hbudget
    _ ≤ (N : ℝ) ^ ((-4 / 5 + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.RetainedBinomialApproximation
