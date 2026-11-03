module

public import PaperP1.Model.CoreCanonicalComponents
public import PaperP1.Asymptotics.NoSingletonJointMassUnderInputs
public import PaperP1.Asymptotics.HighNullityPairMassUnderInputs

/-! # Every bounded order of positive-projection cores above half a window rank has joint mass rate1 -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedPositiveCoreMassUnderInputs

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.CoarseConnectedParameters PaperP1.RelationCoreWitnesses

theorem uniform_bound (R t : ℕ) (v C ε : ℝ) (ht : 2 ≤ t) (hv : 0 < v) (hε : 0 < ε) :
    ∃ pc : Parameters R, ∃ pp : FinitePairDeficitInputs.Parameters,
      Hypotheses pc (ε / 16) →
      FinitePairDeficitInputs.Hypotheses pp (GeneralGraphHostCount.sizeCap (ε / 128)) →
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        ∀ G : Finset ℕ, G ⊆ dyadicBlock N → ∀ F : Finset (Finset ℕ),
        (∀ I ∈ F, I ⊆ G ∧ 2 ≤ I.card ∧ I.card ≤ R ∧ Core t L I ∧
          (L : ℝ) / 2 < runRelativeNullity L I) →
        (∑ I ∈ F, v ^ I.card * infiniteJointMoment L I) ≤ (N : ℝ) ^ (-1 + ε) := by
  classical
  obtain ⟨pc, hc⟩ := NoSingletonJointMassUnderInputs.uniform_weighted R v C (ε / 2) hv.le (by positivity)
  obtain ⟨pp, hp⟩ := HighNullityPairMassUnderInputs.uniform_mass v C (ε / 2) hv.le (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨pc, pp, ?_⟩
  intro hgeoC hgeoP
  have hsC : (ε / 2) / 8 = ε / 16 := by ring
  have hsP : (ε / 2) / 64 = ε / 128 := by ring
  obtain ⟨NC, _hNC, hc⟩ := hc (by simpa only [hsC] using hgeoC)
  obtain ⟨NP, _hNP, hp⟩ := hp (by simpa only [hsP] using hgeoP)
  refine ⟨10 + NC + NP + NF, by omega, ?_⟩
  intro N hN L hband G hG F hF
  let P := fun I : Finset ℕ ↦ I.card = 2
  let FP := F.filter P
  let FH := F.filter fun I ↦ ¬ P I
  have hpair : (∑ I ∈ FP, v ^ I.card * infiniteJointMoment L I) ≤ (N : ℝ) ^ (-1 + ε / 2) := by
    apply hp N (by omega) L hband FP
    intro I hI
    obtain ⟨hIF, htwo⟩ := mem_filter.mp hI
    obtain ⟨hIG, _hlower, _hupper, _hcore, hstrong⟩ := hF I hIF
    exact ⟨hIG.trans hG, htwo, hstrong⟩
  have hhigher : (∑ I ∈ FH, v ^ I.card * infiniteJointMoment L I) ≤ (N : ℝ) ^ (-1 + ε / 2) := by
    apply hc N (by omega) L hband G hG FH
    intro I hI
    obtain ⟨hIF, hnottwo⟩ := mem_filter.mp hI
    obtain ⟨hIG, hlower, hupper, hcore, _hstrong⟩ := hF I hIF
    exact ⟨hIG, by dsimp only [P] at hnottwo; omega, hupper,
      fun C hC ↦ CoreCanonicalComponents.block_card t L ht I hcore C hC⟩
  have hsplit := sum_filter_add_sum_filter_not F P (fun I ↦ v ^ I.card * infiniteJointMoment L I)
  change (∑ I ∈ FP, v ^ I.card * infiniteJointMoment L I) +
    (∑ I ∈ FH, v ^ I.card * infiniteJointMoment L I) = _ at hsplit
  have hfactor : 2 * (N : ℝ) ^ (-1 + ε / 2) ≤ (N : ℝ) ^ (-1 + ε) := by
    convert hf N (by omega) using 1
    congr 1
    ring
  linarith only [hpair, hhigher, hsplit, hfactor]

end PaperP1.FixedPositiveCoreMassUnderInputs
