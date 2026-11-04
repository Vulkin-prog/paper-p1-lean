module

public import PaperP1.Asymptotics.SharpStrongExactMassUnderInputs
public import PaperP1.Asymptotics.StrongExactTripleActivityReductionUnderInputs
public import PaperP1.Asymptotics.CoarseThirdCumulantUnderBCN

/-! # The full actual third activity and factorial cumulant at the sharp41/30 scale

The existing BCN premise and finite geometric properties remain explicit.
The effective-crossing host restriction removes any need for the unresolved
sharp31/24 asymmetric raw-loss profile or a Reuss7/12 input.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SharpThirdActivityUnderInputs

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.ConnectedWindowFamilies
  PaperP1.WeakExactTripleMassUnderBCN

local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem uniform_joint_mass (c κ : ℝ) (hc : 0 < c) (hBCN : PlaneCurvePointCount.UniformBound c κ)
    (C ε : ℝ) (hε : 0 < ε) :
    ∃ Q : ℕ, 1 ≤ Q ∧ ∃ p : (ab : FiniteInteriorUnitEdges.channels Q) → FiniteCompressedInteriorMass.Parameters,
      (∀ ab, FiniteCompressedInteriorMass.Hypotheses (p ab) ab.val.2 (ε / 8)) →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        ∀ F : Finset (Finset ℕ), F ⊆ connectedFamilies G L 3 →
        (∑ T ∈ F, infiniteJointMoment L T) ≤ (N : ℝ) ^ (-41 / 30 + ε) := by
  obtain ⟨θ, hθ, Nw, _hNw, hw⟩ := WeakExactTripleMassUnderBCN.uniform_reduction
    c κ hc hBCN C (ε / 2) (by positivity)
  obtain ⟨Q, hQ, p, hs⟩ := SharpStrongExactMassUnderInputs.uniform_mass θ C (ε / 2) hθ (by positivity)
  obtain ⟨Nf, hf⟩ := HalfCountSchedule.factor_absorption 2 (-41 / 30 + ε / 2) (ε / 2) (by positivity)
  refine ⟨Q, hQ, p, ?_⟩
  intro hgeo
  obtain ⟨Ns, _hNs, hs⟩ := hs (by simpa only [div_div, show (2 : ℝ) * 4 = 8 by norm_num] using hgeo)
  refine ⟨max 4 (max Nw (max Ns Nf)), by omega, ?_⟩
  intro N hN L hcrit G hG F hF
  have hdata (T : Finset ℕ) (hT : T ∈ F) : T ⊆ dyadicBlock N ∧ T.card = 3 ∧ Connected L T := by
    obtain ⟨hTp, hconn⟩ := mem_filter.mp (hF hT)
    obtain ⟨hTG, hcard⟩ := mem_powersetCard.mp hTp
    exact ⟨hTG.trans hG, hcard, hconn⟩
  have hweak := hw N (by omega) L hcrit F hdata
  have hstrong := hs N (by omega) L hcrit (F.filter (StrongExactPair L θ)) (by
    intro T hT
    obtain ⟨hTF, hstrong⟩ := mem_filter.mp hT
    obtain ⟨hTN, hcard, hconn⟩ := hdata T hTF
    exact ⟨hTN, hcard, hconn, hstrong⟩)
  have herror : (N : ℝ) ^ (-3 / 2 + ε / 2) ≤ (N : ℝ) ^ (-41 / 30 + ε / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega)) (by linarith)
  calc
    _ ≤ 2 * (N : ℝ) ^ (-41 / 30 + ε / 2) := by linarith only [hweak, hstrong, herror]
    _ ≤ _ := by
      simpa only [show (-41 / 30 + ε / 2) + ε / 2 = -41 / 30 + ε by ring] using hf N (by omega)

theorem uniform_absolute_activity (c κ : ℝ) (hc : 0 < c) (hBCN : PlaneCurvePointCount.UniformBound c κ)
    (C ε : ℝ) (hε : 0 < ε) :
    ∃ Q : ℕ, 1 ≤ Q ∧ ∃ p : (ab : FiniteInteriorUnitEdges.channels Q) → FiniteCompressedInteriorMass.Parameters,
      ∃ pe : FinitePairDeficitInputs.Parameters,
      (∀ ab, FiniteCompressedInteriorMass.Hypotheses (p ab) ab.val.2 (ε / 16)) →
      FinitePairDeficitInputs.Hypotheses pe (GeneralGraphHostCount.sizeCap (ε / 2048)) →
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        CompatibleActivitySplit.absolute L (G.powersetCard 3) ≤ (N : ℝ) ^ (-41 / 30 + ε) := by
  obtain ⟨Q, hQ, p, hj⟩ := uniform_joint_mass c κ hc hBCN C (ε / 2) (by positivity)
  obtain ⟨pe, he⟩ := ConnectedTriplePositiveUnderInputs.uniform_absolute_error C (ε / 2) (by positivity)
  obtain ⟨Ng, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨Nf, hf⟩ := HalfCountSchedule.factor_absorption 2 (-41 / 30 + ε / 2) (ε / 2) (by positivity)
  refine ⟨Q, hQ, p, pe, ?_⟩
  intro hgeo hgeoE
  obtain ⟨Nj, _hNj, hj⟩ := hj (by simpa only [div_div, show (2 : ℝ) * 8 = 16 by norm_num] using hgeo)
  obtain ⟨Ne, _hNe, he⟩ := he (by simpa only [div_div, show (2 : ℝ) * 1024 = 2048 by norm_num] using hgeoE)
  refine ⟨max 10 (max Nj (max Ne (max Ng Nf))), by omega, ?_⟩
  intro N hN L hcrit G hG
  let H := PositiveMarginalRestriction.positiveGround G L
  have hHG : H ⊆ G := PositiveMarginalRestriction.positiveGround_subset G L
  have hHN : H ⊆ dyadicBlock N := hHG.trans hG
  have hpos : ∀ x ∈ H, 0 < infiniteMarginal x L := fun _ hx ↦ PositiveMarginalRestriction.marginal_positive hx
  have hL : 0 < L := by have hh := (hg N (by omega) L hcrit).2.2.1; omega
  have hrestrict : CompatibleActivitySplit.absolute L (G.powersetCard 3) =
      CompatibleActivitySplit.absolute L (connectedFamilies H L 3) := by
    calc
      _ = CompatibleActivitySplit.absolute L (H.powersetCard 3) :=
        PositiveMarginalRestriction.sum_restrict G L 3 abs abs_zero
      _ = _ := SharpThirdCancellationUnderInputs.connected_activity_eq H L hL hpos
  have hmass := hj N (by omega) L hcrit H hHN (connectedFamilies H L 3) (subset_refl _)
  have herror := (abs_le.mp (he N (by omega) L hcrit H hHN)).1
  have hpower : (N : ℝ) ^ (-3 / 2 + ε / 2) ≤ (N : ℝ) ^ (-41 / 30 + ε / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega)) (by linarith)
  have hfactor : 2 * (N : ℝ) ^ (-41 / 30 + ε / 2) ≤ (N : ℝ) ^ (-41 / 30 + ε) := by
    simpa only [show (-41 / 30 + ε / 2) + ε / 2 = -41 / 30 + ε by ring] using hf N (by omega)
  rw [hrestrict]
  change -(N : ℝ) ^ (-3 / 2 + ε / 2) ≤ (∑ T ∈ connectedFamilies H L 3, infiniteJointMoment L T) -
    CompatibleActivitySplit.absolute L (connectedFamilies H L 3) at herror
  linarith only [hmass, herror, hpower, hfactor]

theorem uniform_cumulant (c κ : ℝ) (hc : 0 < c) (hBCN : PlaneCurvePointCount.UniformBound c κ)
    (C ε : ℝ) (hε : 0 < ε) :
    ∃ Q : ℕ, 1 ≤ Q ∧ ∃ p : (ab : FiniteInteriorUnitEdges.channels Q) → FiniteCompressedInteriorMass.Parameters,
      ∃ pe : FinitePairDeficitInputs.Parameters,
      (∀ ab, FiniteCompressedInteriorMass.Hypotheses (p ab) ab.val.2 (ε / 32)) →
      FinitePairDeficitInputs.Hypotheses pe (GeneralGraphHostCount.sizeCap (ε / 4096)) →
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        |ThirdRunFactorialCumulant.thirdFactorialCumulant G L| ≤ (N : ℝ) ^ (-41 / 30 + ε) := by
  obtain ⟨Q, hQ, p, pe, ha⟩ := uniform_absolute_activity c κ hc hBCN C (ε / 2) (by positivity)
  obtain ⟨Nr, _hNr, hr⟩ := CoarseThirdCumulantUnderBCN.uniform_repeated_cost c κ hc hBCN C (ε / 2) (by positivity)
  obtain ⟨Nf, hf⟩ := HalfCountSchedule.factor_absorption 7 (-41 / 30 + ε / 2) (ε / 2) (by positivity)
  refine ⟨Q, hQ, p, pe, ?_⟩
  intro hgeo hgeoE
  obtain ⟨Na, _hNa, ha⟩ := ha (by simpa only [div_div, show (2 : ℝ) * 16 = 32 by norm_num] using hgeo)
    (by simpa only [div_div, show (2 : ℝ) * 2048 = 4096 by norm_num] using hgeoE)
  refine ⟨max 10 (max Na (max Nr Nf)), by omega, ?_⟩
  intro N hN L hcrit G hG
  have hactivity := ha N (by omega) L hcrit G hG
  have hrepeat := (hr N (by omega) L hcrit G hG).trans
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega))
      (by linarith : (-3 / 2 : ℝ) + ε / 2 ≤ -41 / 30 + ε / 2))
  have hsigned : |CompatibleActivitySplit.signed L (G.powersetCard 3)| ≤
      CompatibleActivitySplit.absolute L (G.powersetCard 3) := abs_sum_le_sum_abs _ _
  have hfactor : 7 * (N : ℝ) ^ (-41 / 30 + ε / 2) ≤ (N : ℝ) ^ (-41 / 30 + ε) := by
    simpa only [show (-41 / 30 + ε / 2) + ε / 2 = -41 / 30 + ε by ring] using hf N (by omega)
  rw [ThirdRunActivityComparison.exact_decomposition hG]
  calc
    _ ≤ |6 * CompatibleActivitySplit.signed L (G.powersetCard 3)| +
        |RepeatedIndexCost.cost (fun x ↦ infiniteMarginal x L) (infiniteCenteredCoefficient L) G| := abs_add_le _ _
    _ = 6 * |CompatibleActivitySplit.signed L (G.powersetCard 3)| +
        |RepeatedIndexCost.cost (fun x ↦ infiniteMarginal x L) (infiniteCenteredCoefficient L) G| := by
      rw [abs_mul]
      norm_num
    _ ≤ (N : ℝ) ^ (-41 / 30 + ε) := by linarith only [hsigned, hactivity, hrepeat, hfactor]

end PaperP1.SharpThirdActivityUnderInputs
