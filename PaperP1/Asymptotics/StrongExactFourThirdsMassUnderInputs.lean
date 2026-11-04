module

public import PaperP1.Asymptotics.StrongExactFiniteChannelCover
public import PaperP1.Asymptotics.FiniteCompressedInteriorMass
public import PaperP1.Asymptotics.HeightTwoBoundaryJointMass

/-! # All strong exact connected triples have four-thirds mass under finite geometric inputs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.StrongExactFourThirdsMassUnderInputs

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.ConnectedWindowFamilies
  PaperP1.WeakExactTripleMassUnderBCN

local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem uniform_mass (θ C ε : ℝ) (hθ : 0 < θ) (hε : 0 < ε) :
    ∃ Q : ℕ, 1 ≤ Q ∧ ∃ p : (ab : FiniteInteriorUnitEdges.channels Q) → FiniteCompressedInteriorMass.Parameters,
      (∀ ab, FiniteCompressedInteriorMass.Hypotheses (p ab) ab.val.2 (ε / 4)) →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ F : Finset (Finset ℕ),
        (∀ T ∈ F, T ⊆ dyadicBlock N ∧ T.card = 3 ∧ Connected L T ∧ StrongExactPair L θ T) →
        (∑ T ∈ F, infiniteJointMoment L T) ≤ (N : ℝ) ^ (-4 / 3 + ε) := by
  obtain ⟨Q, hQ, hcover⟩ := StrongExactFiniteChannelCover.uniform_cover θ hθ
  obtain ⟨Nc, _hNc, hc⟩ := hcover C
  obtain ⟨p, hi⟩ := FiniteCompressedInteriorMass.uniform_mass Q C (ε / 2) (by positivity)
  obtain ⟨Nb, _hNb, hb⟩ := HeightTwoBoundaryJointMass.uniform_triples C (ε / 2) (by positivity)
  obtain ⟨Nf, hf⟩ := HalfCountSchedule.factor_absorption 2 (-4 / 3 + ε / 2) (ε / 2) (by positivity)
  refine ⟨Q, hQ, p, ?_⟩
  intro hgeo
  obtain ⟨Ni, _hNi, hi⟩ := hi (by simpa only [div_div, show (2 : ℝ) * 2 = 4 by norm_num] using hgeo)
  refine ⟨max 4 (max Nc (max Ni (max Nb Nf))), by omega, ?_⟩
  intro N hN L hcrit F hF
  let P := F.filter fun T ↦ 0 < infiniteJointMoment L T
  let B := P.filter fun T ↦ ∃ e ∈ BoundaryAlignedPairs.channel N L 1 2, e ⊆ T
  let I := P.filter fun T ↦ T ∈ FiniteCompressedInteriorMass.hosts N L Q
  have hPF : P ⊆ F := filter_subset _ _
  have hsum : (∑ T ∈ P, infiniteJointMoment L T) = ∑ T ∈ F, infiniteJointMoment L T := by
    apply sum_subset hPF
    intro T _hTF hnot
    have hh : ¬0 < infiniteJointMoment L T := by
      intro hh
      exact hnot (mem_filter.mpr ⟨_hTF, hh⟩)
    exact le_antisymm (le_of_not_gt hh) (infiniteJointMoment_nonneg L T)
  have hcover : P ⊆ B ∪ I := by
    intro T hT
    obtain ⟨hTF, hpos⟩ := mem_filter.mp hT
    obtain ⟨hTN, hcard, hconn, hstrong⟩ := hF T hTF
    rcases hc N (by omega) L hcrit T hTN hcard hconn hstrong hpos with hB | hI
    · exact mem_union_left _ (mem_filter.mpr ⟨hT, hB⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hT, FiniteCompressedInteriorMass.mem_hosts.mpr hI⟩)
  have hboundary : (∑ T ∈ B, infiniteJointMoment L T) ≤ (N : ℝ) ^ (-4 / 3 + ε / 2) := by
    have hh := hb N (by omega) L hcrit B (by
      intro T hT
      obtain ⟨hTP, hTB⟩ := mem_filter.mp hT
      obtain ⟨hTN, hcard, _hconn, _hstrong⟩ := hF T (hPF hTP)
      exact ⟨hTN, hcard, hTB⟩)
    exact hh.trans (Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (show 1 ≤ N by omega)) (by linarith : (-3 / 2 : ℝ) + ε / 2 ≤ -4 / 3 + ε / 2))
  have hinterior : (∑ T ∈ I, infiniteJointMoment L T) ≤ (N : ℝ) ^ (-4 / 3 + ε / 2) :=
    (sum_le_sum_of_subset_of_nonneg (fun _ hT ↦ (mem_filter.mp hT).2)
      (fun T _ _ ↦ infiniteJointMoment_nonneg L T)).trans (hi N (by omega) L hcrit)
  have h0 := sum_le_sum_of_subset_of_nonneg hcover (fun T _ _ ↦ infiniteJointMoment_nonneg L T)
  have h1 := GraphStarWeights.sum_union_le_nonneg B I (infiniteJointMoment L) (infiniteJointMoment_nonneg L)
  have hfactor : 2 * (N : ℝ) ^ (-4 / 3 + ε / 2) ≤ (N : ℝ) ^ (-4 / 3 + ε) := by
    simpa only [show (-4 / 3 + ε / 2) + ε / 2 = -4 / 3 + ε by ring] using hf N (by omega)
  rw [← hsum]
  linarith only [hboundary, hinterior, h0, h1, hfactor]

end PaperP1.StrongExactFourThirdsMassUnderInputs
