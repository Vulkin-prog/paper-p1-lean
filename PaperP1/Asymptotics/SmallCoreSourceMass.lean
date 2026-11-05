module

public import PaperP1.Asymptotics.SmallCoreJointMass
public import PaperP1.Asymptotics.SmallCorePairMass
public import PaperP1.Asymptotics.SmallCoreDeficitReduction

/-! # All small compatible core sources and their actual connected closures have joint-deficit rate3/2 -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmallCoreSourceMass

open Finset Filter PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts

theorem uniform_source (v C ε : ℝ) (hv : 0 < v) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        SmallCoreFamilyCover.sourceMass G L v ≤ (N : ℝ) ^ (-3 / 2 + ε) := by
  obtain ⟨NC, _hNC, hc⟩ := SmallCoreJointMass.uniform_source v C (ε / 2) hv (by positivity)
  obtain ⟨NP, _hNP, hp⟩ := SmallCorePairMass.uniform_pair_source v C (ε / 2) hv (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 (-3 / 2 + ε / 2) (ε / 2) (by positivity)
  refine ⟨10 + NC + NP + NF, by omega, ?_⟩
  intro N hN L hband G hG
  have hsmall := hc N (by omega) L hband G hG
  have hpair := hp N (by omega) L hband G hG
  dsimp only [FixedPairExtensions.sourceSpace] at hpair
  have hsplit := SmallCorePairDeficit.source_split G L v
  have hfactor : 2 * (N : ℝ) ^ (-3 / 2 + ε / 2) ≤ (N : ℝ) ^ (-3 / 2 + ε) := by
    convert hf N (by omega) using 1
    congr 1
    ring
  linarith only [hsmall, hpair, hsplit, hfactor]

theorem uniform_families (K : ℕ → ℕ)
    (hK : Tendsto (fun N : ℕ ↦ (K N : ℝ) / Real.log N) atTop (nhds 0))
    (u C ε : ℝ) (hu : 0 < u) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        ∀ G : Finset ℕ, G ⊆ dyadicBlock N → ∀ F : Finset (Finset ℕ),
        (∀ I ∈ F, I ⊆ G ∧ ConnectedWindowFamilies.Connected L I ∧ 256 < I.card ∧ I.card ≤ K N ∧
          (L : ℝ) / 60 < (runCompatibleNullity L I : ℝ) ∧ (ChosenRelationCore.core L I).card < 256) →
        (∑ I ∈ F, u ^ I.card * |infiniteCenteredCoefficient L I|) ≤ (N : ℝ) ^ (-3 / 2 + ε) := by
  obtain ⟨NS, _hNS, hs⟩ := uniform_source (512 * u) C ε (by positivity) hε
  obtain ⟨NK, _hNK, hk⟩ := SublogCardinalityCap.uniform_cap K hK C (1 / 960) (by norm_num)
  obtain ⟨NF, hf⟩ := SaturationDegrees.finite_conditions C 12 (by norm_num)
  refine ⟨10 + NS + NK + NF, by omega, ?_⟩
  intro N hN L hband G hG F hF
  have hB : 2 ≤ L + 1 := (hf N (by omega) L hband).2.1
  have hL : 0 < L := by omega
  have hdata : ∀ I ∈ F, I ⊆ G ∧ ConnectedWindowFamilies.Connected L I ∧ 256 < I.card ∧
      2 ≤ (ChosenRelationCore.core L I).card ∧ (ChosenRelationCore.core L I).card < 256 := by
    intro I hI
    obtain ⟨hIG, hconn, hlarge, hsize, hhigh, hsmall⟩ := hF I hI
    have hsizeR : (I.card : ℝ) ≤ (L : ℝ) / 960 := by
      have hIR : (I.card : ℝ) ≤ K N := by exact_mod_cast hsize
      have hKR := hk N (by omega) L hband
      linarith only [hIR, hKR]
    exact ⟨hIG, hconn, hlarge, SmallCoreRankRetention.size_two L hL I hsizeR hhigh, hsmall⟩
  exact (SmallCoreFamilyCover.finite_bound G L hL u hu.le F hdata).trans (hs N (by omega) L hband G hG)

end PaperP1.SmallCoreSourceMass
