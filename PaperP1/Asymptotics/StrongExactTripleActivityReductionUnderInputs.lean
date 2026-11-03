module

public import PaperP1.Asymptotics.WeakExactTripleMassUnderBCN
public import PaperP1.Asymptotics.ConnectedTriplePositiveUnderInputs
public import PaperP1.Asymptotics.SharpThirdCancellationUnderInputs
public import PaperP1.Model.PositiveMarginalRestriction

/-! # The full third absolute activity reduces to strong exact-alignment triples

The coefficient of the remaining actual joint mass is one. Zero-marginal
windows are removed by an exact identity, with no regularity hypothesis.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.StrongExactTripleActivityReductionUnderInputs

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.ConnectedWindowFamilies PaperP1.WeakExactTripleMassUnderBCN

local instance strongExactTripleActivityDecidable (P : Prop) : Decidable P := Classical.propDecidable P

theorem uniform_reduction (c κ : ℝ) (hc : 0 < c) (hBCN : PlaneCurvePointCount.UniformBound c κ)
    (C ε : ℝ) (hε : 0 < ε) :
    ∃ θ : ℝ, 0 < θ ∧ ∃ p : FinitePairDeficitInputs.Parameters,
      FinitePairDeficitInputs.Hypotheses p (GeneralGraphHostCount.sizeCap (ε / 2048)) →
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        CompatibleActivitySplit.absolute L (G.powersetCard 3) ≤
          (∑ I ∈ (connectedFamilies G L 3).filter (StrongExactPair L θ), infiniteJointMoment L I) +
          (N : ℝ) ^ (-3 / 2 + ε) := by
  obtain ⟨θ, hθ, NM, _hNM, hm⟩ := WeakExactTripleMassUnderBCN.uniform_reduction
    c κ hc hBCN C (ε / 2) (by positivity)
  obtain ⟨p, hp⟩ := ConnectedTriplePositiveUnderInputs.uniform_absolute_error C (ε / 2) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption 2 (-3 / 2 + ε / 2) (ε / 2) (by positivity)
  refine ⟨θ, hθ, p, ?_⟩
  intro hgeo
  have hscale : (ε / 2) / 1024 = ε / 2048 := by ring
  obtain ⟨NE, _hNE, he⟩ := hp (by simpa only [hscale] using hgeo)
  refine ⟨10 + NM + NG + NA + NE, by omega, ?_⟩
  intro N hN L hband G hG
  classical
  have hL : 0 < L := by have hh := hg N (by omega) L hband; omega
  let H := PositiveMarginalRestriction.positiveGround G L
  have hHG : H ⊆ G := PositiveMarginalRestriction.positiveGround_subset G L
  have hHN : H ⊆ dyadicBlock N := hHG.trans hG
  have hpos (x : ℕ) (hx : x ∈ H) : 0 < infiniteMarginal x L :=
    PositiveMarginalRestriction.marginal_positive hx
  have hrestrict : CompatibleActivitySplit.absolute L (G.powersetCard 3) =
      CompatibleActivitySplit.absolute L (connectedFamilies H L 3) := by
    calc
      _ = CompatibleActivitySplit.absolute L (H.powersetCard 3) :=
        PositiveMarginalRestriction.sum_restrict G L 3 abs (abs_zero)
      _ = _ := SharpThirdCancellationUnderInputs.connected_activity_eq H L hL hpos
  have hmass := hm N (by omega) L hband (connectedFamilies H L 3) (by
    intro I hI
    obtain ⟨hpower, hconn⟩ := mem_filter.mp hI
    obtain ⟨hIH, hcard⟩ := mem_powersetCard.mp hpower
    exact ⟨hIH.trans hHN, hcard, hconn⟩)
  have herror := (abs_le.mp (he N (by omega) L hband H hHN)).1
  have hsub : (connectedFamilies H L 3).filter (StrongExactPair L θ) ⊆
      (connectedFamilies G L 3).filter (StrongExactPair L θ) := by
    intro I hI
    obtain ⟨hconn, hstrong⟩ := mem_filter.mp hI
    obtain ⟨hpower, hconn⟩ := mem_filter.mp hconn
    obtain ⟨hIH, hcard⟩ := mem_powersetCard.mp hpower
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_powersetCard.mpr ⟨hIH.trans hHG, hcard⟩, hconn⟩, hstrong⟩
  have hsum := sum_le_sum_of_subset_of_nonneg hsub (fun I _ _ ↦ infiniteJointMoment_nonneg L I)
  have hfactor : 2 * (N : ℝ) ^ (-3 / 2 + ε / 2) ≤ (N : ℝ) ^ (-3 / 2 + ε) := by
    convert ha N (by omega) using 1
    congr 1
    ring
  rw [hrestrict]
  change (∑ I ∈ connectedFamilies H L 3, infiniteJointMoment L I) -
    CompatibleActivitySplit.absolute L (connectedFamilies H L 3) ≥ -(N : ℝ) ^ (-3 / 2 + ε / 2) at herror
  linarith only [hmass, herror, hsum, hfactor]

end PaperP1.StrongExactTripleActivityReductionUnderInputs
