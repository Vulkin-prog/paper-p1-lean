module

public import PaperP1.Model.DensePairCrossingSeeds
public import PaperP1.Asymptotics.DensePairCrossingSeedsUnderInputs
public import PaperP1.Asymptotics.UnorderedSeedMassPropagation
public import PaperP1.Model.CompatibleTripleJointBound

/-! # Every dense minimal pair-crossing seed and fixed compatible extension has the stronger five-thirds scale -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DensePairCrossingFamiliesUnderInputs

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts

theorem uniform_seeds (C η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ pd : DensePrimitiveTripleMassUnderInputs.Parameters, ∃ pp : FinitePairDeficitInputs.Parameters,
      (DensePrimitiveTripleMassUnderInputs.Hypotheses pd →
      FinitePairDeficitInputs.Hypotheses pp (GeneralGraphHostCount.sizeCap (ε / 2048)) →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        (∑ I ∈ DensePairCrossingSeeds.families G L η, infiniteJointMoment L I) ≤
          (N : ℝ) ^ (-5 / 3 + ε)) := by
  obtain ⟨pd, pp, hp⟩ := DensePairCrossingSeedsUnderInputs.uniform_bound C η ε hη hε
  refine ⟨pd, pp, ?_⟩
  intro hgeoD hgeoP
  obtain ⟨N₀, hN₀, hh⟩ := hp hgeoD hgeoP
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband G hG
  have hsum := hh N hN L hband G hG (DensePairCrossingSeeds.targets G L η) (by
    intro e _he p hp
    have hm := (DensePairCrossingSeeds.mem_targets G L η e p).mp hp
    exact ⟨hG hm.1, hG hm.2.1, hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2.1⟩) (by
    intro e _he p hp
    exact ((DensePairCrossingSeeds.mem_targets G L η e p).mp hp).2.2.2.2.2.1) (by
    intro e _he p hp
    exact ((DensePairCrossingSeeds.mem_targets G L η e p).mp hp).2.2.2.2.2.2)
  exact (DensePairCrossingSeeds.mass_bound G L η).trans hsum

theorem uniform_centered_extensions (k : ℕ) (C η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ pd : DensePrimitiveTripleMassUnderInputs.Parameters, ∃ pp : FinitePairDeficitInputs.Parameters,
      (DensePrimitiveTripleMassUnderInputs.Hypotheses pd →
      FinitePairDeficitInputs.Hypotheses pp (GeneralGraphHostCount.sizeCap (ε / 8192)) →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        ∀ F : Finset (Finset ℕ),
        (∀ I ∈ F, I ⊆ G ∧ I.card = 4 + k ∧ 0 < infiniteJointMoment L I ∧
          ∃ D ∈ DensePairCrossingSeeds.families G L η, D ⊆ I) →
        (∑ I ∈ F, |infiniteCenteredCoefficient L I|) ≤ (N : ℝ) ^ (-5 / 3 + ε)) := by
  obtain ⟨pd, pp, hp⟩ := uniform_seeds C η (ε / 4) hη (by positivity)
  obtain ⟨NR, hr⟩ := UnorderedSeedMassPropagation.uniform_mass 4 (by decide) k C (ε / 4) (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption ((2 : ℝ) ^ (4 + k) * (4 + k).factorial)
    (-5 / 3 + ε / 2) (ε / 2) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨pd, pp, ?_⟩
  intro hgeoD hgeoP
  have hscale : (ε / 4) / 2048 = ε / 8192 := by ring
  obtain ⟨NS, _hNS, hs⟩ := hp hgeoD (by simpa only [hscale] using hgeoP)
  refine ⟨4 + NS + NR + NF + NG, by omega, ?_⟩
  intro N hN L hband G hG F hF
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hseed := hs N (by omega) L hband G hG
  have hprop := hr N (by omega) L hL hband (DensePairCrossingSeeds.families G L η) (by
    intro D hD
    have hd := DensePairCrossingSeeds.family_data G L η D hD
    exact ⟨hd.1.trans hG, hd.2.1⟩) F (by
    intro I hI
    have hi := hF I hI
    exact ⟨hi.1.trans hG, hi.2.1, hi.2.2.2⟩)
  have hmass : (∑ I ∈ F, infiniteJointMoment L I) ≤
      ((4 + k).factorial : ℝ) * (N : ℝ) ^ (-5 / 3 + ε / 2) := by
    calc
      _ ≤ ((4 + k).factorial : ℝ) * (N : ℝ) ^ (ε / 4) *
          (N : ℝ) ^ (-5 / 3 + ε / 4) := hprop.trans
        (mul_le_mul_of_nonneg_left hseed (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hn.le _)))
      _ = _ := by rw [mul_assoc, ← Real.rpow_add hn]; congr 1; ring
  calc
    _ ≤ ∑ I ∈ F, (2 : ℝ) ^ (4 + k) * infiniteJointMoment L I := by
      apply sum_le_sum
      intro I hI
      have hi := hF I hI
      simpa only [hi.2.1] using CompatibleTripleJointBound.centered_compatible_bound L I hL hi.2.2.1
    _ = (2 : ℝ) ^ (4 + k) * ∑ I ∈ F, infiniteJointMoment L I := by rw [mul_sum]
    _ ≤ (2 : ℝ) ^ (4 + k) * (((4 + k).factorial : ℝ) * (N : ℝ) ^ (-5 / 3 + ε / 2)) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = ((2 : ℝ) ^ (4 + k) * (4 + k).factorial) * (N : ℝ) ^ (-5 / 3 + ε / 2) := by ring
    _ ≤ (N : ℝ) ^ ((-5 / 3 + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.DensePairCrossingFamiliesUnderInputs
