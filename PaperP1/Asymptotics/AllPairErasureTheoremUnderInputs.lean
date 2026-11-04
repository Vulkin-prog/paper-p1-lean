module

public import PaperP1.Asymptotics.OnceErasedPoissonUnderInputs
public import PaperP1.Asymptotics.OriginalHermiteCountUnderInputs

/-! # Complete companion T19.14 under the recorded finite geometric inputs

The final first-order criteria use the full-field rate four-fifths. The
sharper two-edge O(a_N^2) estimate is not assumed or asserted here.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AllPairErasureTheoremUnderInputs

open PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.Model.InfiniteRademacher PaperP1.PositionalFiniteLaw
  PaperP1.AllPairOriginalLaws PaperP1.AllPairCountMeans PaperP1.AllPairResidualMass
  PaperP1.AllPairCriteriaUnderInputs PaperP1.CriticalPairNegligible
  PaperP1.OriginalHermiteCountUnderInputs

structure CriterionParameters where
  allPairs : FinitePairDeficitInputs.Parameters
  isolatedField : RetainedComponentActivityUnderInputs.Parameters
  isolatedMean : CoarseConnectedParameters.Parameters 4
  onceField : RetainedComponentActivityUnderInputs.Parameters
  onceMean : CoarseConnectedParameters.Parameters 4
  hermiteField : RetainedComponentActivityUnderInputs.Parameters

structure CriterionHypotheses (p : CriterionParameters) : Prop where
  allPairs : FinitePairDeficitInputs.Hypotheses p.allPairs (GeneralGraphHostCount.sizeCap (1 / 15360))
  isolatedField : RetainedComponentActivityUnderInputs.Hypotheses p.isolatedField (1 / 3840)
  isolatedMean : CoarseConnectedParameters.Hypotheses p.isolatedMean (1 / 960)
  onceField : RetainedComponentActivityUnderInputs.Hypotheses p.onceField (1 / 3840)
  onceMean : CoarseConnectedParameters.Hypotheses p.onceMean (1 / 960)
  hermiteField : RetainedComponentActivityUnderInputs.Hypotheses p.hermiteField (1 / 960)

def retainedField (N L : ℕ) (ω : InfiniteSample) : Configuration ℕ :=
  PositionalPairDeletion.isolate (AllPairDependencyGraph.edges (RegularStarts.regularStarts N L) L)
    (PositionalAllPairCost.restrict (RegularStarts.regularStarts N L)
      (configuration (dyadicBlock N) (fun x ↦ infiniteStartIndicator x L) ω))

theorem allCount_eq_total (N L : ℕ) (ω : InfiniteSample) :
    allCount N L ω = PositionalCountProjection.totalCount (retainedField N L ω) := rfl

theorem retained_geometry (N L : ℕ) (ω : InfiniteSample) (x y : ℕ) (hxy : x < y)
    (hx : 0 < retainedField N L ω x) (hy : 0 < retainedField N L ω y) :
    x + L < y ∧ Disjoint (squareClassSpace x L) (squareClassSpace y L) :=
  AllPairRetainedGeometry.retained_pair_geometry (dyadicBlock N) (RegularStarts.regularStarts N L)
    (RegularStarts.regularStarts_subset N L) L ω x y hxy hx hy

theorem complete_criteria (C : ℝ) :
    ∃ p : CriterionParameters, CriterionHypotheses p →
      Negligible C allResidual ∧ Negligible C goodPoissonDistance ∧
        Negligible C OnceErasedCount.poissonDistance ∧ HermiteNegligible C ∧
        (Negligible C allResidual ↔ Negligible C goodPoissonDistance) ∧
        (Negligible C allResidual ↔ Negligible C OnceErasedCount.poissonDistance) ∧
        (Negligible C allResidual ↔ HermiteNegligible C) := by
  obtain ⟨pa, ha⟩ := AllPairCriteriaUnderInputs.uniform_criterion_iff C
  obtain ⟨pi, pmi, hi⟩ := ErasedPoissonCountUnderInputs.uniform_relative C
  obtain ⟨pw, pmw, hw⟩ := OnceErasedPoissonUnderInputs.uniform_relative C
  obtain ⟨ph, hh⟩ := OriginalHermiteCountUnderInputs.uniform_relative C
  refine ⟨⟨pa, pi, pmi, pw, pmw, ph⟩, ?_⟩
  intro hgeo
  have hgood := hi hgeo.isolatedField hgeo.isolatedMean
  have honce := hw hgeo.onceField hgeo.onceMean
  have hhermite := hh hgeo.hermiteField
  have hcrit := ha hgeo.allPairs
  have hall := hcrit.2.2.mpr hgood
  exact ⟨hall, hgood, honce, hhermite, hcrit.2.2,
    ⟨fun _ ↦ honce, fun _ ↦ hall⟩, ⟨fun _ ↦ hhermite, fun _ ↦ hall⟩⟩

theorem criteria_on_scale (C c d : ℝ) (hc : 0 < c) (hd : 0 < d) (a : ℕ → ℕ → ℝ)
    (hscale : ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      c * scale N L ≤ a N L ∧ a N L ≤ d * scale N L) :
    ∃ p : CriterionParameters, CriterionHypotheses p →
      (AtScale C a allResidual ↔ AtScale C a goodPoissonDistance) ∧
      (AtScale C a allResidual ↔ AtScale C a OnceErasedCount.poissonDistance) ∧
      (AtScale C a allResidual ↔ HermiteAtScale C a) := by
  obtain ⟨p, hp⟩ := complete_criteria C
  refine ⟨p, ?_⟩
  intro hgeo
  obtain ⟨hall, hgood, honce, hhermite, _hi, _hw, _hh⟩ := hp hgeo
  have hAll := (iff_at_scale C c d hc hd a allResidual hscale).mp hall
  have hGood := (iff_at_scale C c d hc hd a goodPoissonDistance hscale).mp hgood
  have hOnce := (iff_at_scale C c d hc hd a OnceErasedCount.poissonDistance hscale).mp honce
  have hLow : ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → c * scale N L ≤ a N L := by
    obtain ⟨N₁, h⟩ := hscale
    exact ⟨N₁, fun N hN L hband ↦ (h N hN L hband).1⟩
  have hHermite := at_scale_of_lower C c hc a hLow hhermite
  exact ⟨⟨fun _ ↦ hGood, fun _ ↦ hAll⟩, ⟨fun _ ↦ hOnce, fun _ ↦ hAll⟩,
    ⟨fun _ ↦ hHermite, fun _ ↦ hAll⟩⟩

theorem companion_T19_14 (C ε : ℝ) (hε : 0 < ε) :
    ∃ pt pv : FinitePairDeficitInputs.Parameters, ∃ p : CriterionParameters,
      FinitePairDeficitInputs.Hypotheses pt (GeneralGraphHostCount.sizeCap (ε / 256)) →
      FinitePairDeficitInputs.Hypotheses pv (GeneralGraphHostCount.sizeCap (ε / 512)) →
      CriterionHypotheses p →
      (∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        let H : ℝ := (8 * (L + 1) : ℕ)
        tau H N L ≤ (N : ℝ) ^ (-4 / 5 + ε) ∧
        AtomicProbability.totalVariation (goodLaw H N L) (allLaw N L) ≤ tau H N L ∧
        0 ≤ goodMean H N L - allMean N L ∧ goodMean H N L - allMean N L ≤ 2 * tau H N L ∧
        |goodResidual N L - allResidual N L| ≤ (N : ℝ) ^ (-4 / 5 + ε)) ∧
      (Negligible C allResidual ↔ Negligible C goodPoissonDistance) ∧
      (Negligible C allResidual ↔ Negligible C OnceErasedCount.poissonDistance) ∧
      (Negligible C allResidual ↔ HermiteNegligible C) := by
  obtain ⟨pt, ht⟩ := AllPairResidualMassUnderInputs.uniform_tau C ε hε
  obtain ⟨pv, hv⟩ := AllPairOriginalCostsUnderInputs.uniform_bound C ε hε
  obtain ⟨p, hp⟩ := complete_criteria C
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨pt, pv, p, ?_⟩
  intro hτ hV hgeo
  obtain ⟨NT, _hNT, ht⟩ := ht hτ
  obtain ⟨NV, _hNV, hv⟩ := hv hV
  obtain ⟨_hall, _hgood, _honce, _hhermite, hiffGood, hiffOnce, hiffHermite⟩ := hp hgeo
  refine ⟨⟨10 + NT + NV + NG, by omega, ?_⟩, hiffGood, hiffOnce, hiffHermite⟩
  intro N hN L hband
  dsimp only
  let H : ℝ := (8 * (L + 1) : ℕ)
  have hL : 0 < L := by have hh := hg N (by omega) L hband; omega
  have hc := original_cost (by omega : 2 ≤ N) hL H
  have hcost := hv N (by omega) L hband
  have hnonnegTV := AtomicProbability.totalVariation_nonneg (goodLaw H N L) (allLaw N L)
  have hnonnegMean := abs_nonneg (goodMean H N L - allMean N L)
  have herr : |goodResidual N L - allResidual N L| ≤ (N : ℝ) ^ (-4 / 5 + ε) := by
    change _ + _ + |goodResidual N L - allResidual N L| ≤ _ at hcost
    linarith only [hcost, hnonnegTV, hnonnegMean]
  exact ⟨ht N (by omega) L hband, hc.1, hc.2.1, hc.2.2, herr⟩

end PaperP1.AllPairErasureTheoremUnderInputs
