module

public import PaperP1.Model.OriginalDeletedIntensity
public import PaperP1.Asymptotics.DependentPairSecondMomentUnderInputs
public import PaperP1.Asymptotics.NominalMarginalBias

/-! # The finer rate-one intensity assertion of companion T19.10 -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OriginalDeletedIntensityUnderInputs

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.PositionalDeletedFields
  PaperP1.PositionalFactorialCovariance PaperP1.CoarseConnectedParameters

theorem uniform_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : Parameters 4, Hypotheses p (ε / 16) → ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ H : ℝ,
      let G := dyadicBlock N
      let E := GoodEdgeCompression.goodEdges H N L
      let t := fun x ↦ (2 ^ L : ℝ)⁻¹ - PositionalCompoundPoisson.incidence E (infiniteJointMoment L) x
      (∑ x ∈ G, |mean (onceLaw E G L) x - t x|) +
        (∑ x ∈ G, |mean (isolatedLaw E G L) x - t x|) ≤ (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨p, hp⟩ := DependentPairSecondMomentUnderInputs.uniform_good_bound C (ε / 2) (by positivity)
  obtain ⟨NB, _hNB, hb⟩ := NominalMarginalBias.uniform_bound C (ε / 2) (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 4 (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨p, ?_⟩
  intro hgeo
  have hscale : (ε / 2) / 8 = ε / 16 := by ring
  obtain ⟨NS, _hNS, hs⟩ := hp (by simpa only [hscale] using hgeo)
  refine ⟨10 + NB + NF + NS, by omega, ?_⟩
  intro N hN L hband H
  dsimp only
  let G := dyadicBlock N
  let E := GoodEdgeCompression.goodEdges H N L
  have hE : ∀ e ∈ E, e ⊆ G ∧ e.card = 2 := fun e he ↦
    ⟨(RetainedGoodEdges.good_pair_regular (by omega) e he).trans
      (RegularStarts.regularStarts_subset N L), RetainedGoodEdges.good_pair_card H N L e he⟩
  have hfinite := OriginalDeletedIntensity.finite_bounds G L E (fun _ ↦ (2 ^ L : ℝ)⁻¹) hE
  have hbias := hb N (by omega) L hband G Subset.rfl
  have hsecond := hs N (by omega) L hband H
  have hfactor : 4 * (N : ℝ) ^ (-1 + ε / 2) ≤ (N : ℝ) ^ (-1 + ε) := by
    convert hf N (by omega) using 1
    congr 1
    ring
  have hsum := add_le_add hfinite.1 hfinite.2
  exact hsum.trans (by nlinarith only [hbias, hsecond, hfactor])

end PaperP1.OriginalDeletedIntensityUnderInputs
