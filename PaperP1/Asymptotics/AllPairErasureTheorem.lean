module

public import PaperP1.Asymptotics.OnceErasedPoisson
public import PaperP1.Asymptotics.OriginalHermiteCount

/-! # Unconditional complete companion T19.14 for the original filtered counts

The final first-order criteria use the full-field rate four-fifths. The
sharper two-edge O(a_N^2) estimate is not assumed or asserted here.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AllPairErasureTheorem

open PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.Model.InfiniteRademacher PaperP1.PositionalFiniteLaw
  PaperP1.AllPairOriginalLaws PaperP1.AllPairCountMeans PaperP1.AllPairResidualMass
  PaperP1.AllPairCriteria PaperP1.CriticalPairNegligible
  PaperP1.OriginalHermiteCount

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
    Negligible C allResidual ∧ Negligible C goodPoissonDistance ∧
        Negligible C OnceErasedCount.poissonDistance ∧ HermiteNegligible C ∧
        (Negligible C allResidual ↔ Negligible C goodPoissonDistance) ∧
        (Negligible C allResidual ↔ Negligible C OnceErasedCount.poissonDistance) ∧
        (Negligible C allResidual ↔ HermiteNegligible C) := by
  have hcrit := AllPairCriteria.uniform_criterion_iff C
  have hgood := ErasedPoissonCount.uniform_relative C
  have honce := OnceErasedPoisson.uniform_relative C
  have hhermite := OriginalHermiteCount.uniform_relative C
  have hall := hcrit.2.2.mpr hgood
  exact ⟨hall, hgood, honce, hhermite, hcrit.2.2,
    ⟨fun _ ↦ honce, fun _ ↦ hall⟩, ⟨fun _ ↦ hhermite, fun _ ↦ hall⟩⟩

theorem criteria_on_scale (C c d : ℝ) (hc : 0 < c) (hd : 0 < d) (a : ℕ → ℕ → ℝ)
    (hscale : ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      c * scale N L ≤ a N L ∧ a N L ≤ d * scale N L) :
    (AtScale C a allResidual ↔ AtScale C a goodPoissonDistance) ∧
      (AtScale C a allResidual ↔ AtScale C a OnceErasedCount.poissonDistance) ∧
      (AtScale C a allResidual ↔ HermiteAtScale C a) := by
  obtain ⟨hall, hgood, honce, hhermite, _hi, _hw, _hh⟩ := complete_criteria C
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
  obtain ⟨NT, _hNT, ht⟩ := AllPairResidualMass.uniform_tau C ε hε
  obtain ⟨NV, _hNV, hv⟩ := AllPairOriginalCosts.uniform_bound C ε hε
  obtain ⟨_hall, _hgood, _honce, _hhermite, hiffGood, hiffOnce, hiffHermite⟩ := complete_criteria C
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
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

end PaperP1.AllPairErasureTheorem
