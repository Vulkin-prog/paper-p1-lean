module

public import PaperP1.Model.DirectCrossingSeedFamilies
public import PaperP1.Asymptotics.DirectCrossingPairSeedsUnderInputs
public import PaperP1.Asymptotics.UnorderedSeedMassPropagation

/-! # Minimal direct-crossing seeds and all their fixed containing families retain joint rate5/3 -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DirectCrossingSeedFamiliesUnderInputs

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts

theorem uniform_seeds (r : ℕ) (hr : 2 ≤ r) (C ε : ℝ) (hε : 0 < ε) :
    ∃ pd : DensePrimitiveTripleMassUnderInputs.Parameters,
      ∃ pp : FinitePairDeficitInputs.Parameters,
      DensePrimitiveTripleMassUnderInputs.Hypotheses pd →
      FinitePairDeficitInputs.Hypotheses pp (GeneralGraphHostCount.sizeCap (ε / 2048)) →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        (∑ T ∈ DirectCrossingSeedFamilies.families G L r, infiniteJointMoment L T) ≤
          (N : ℝ) ^ (-5 / 3 + ε) := by
  obtain ⟨pd, pp, h⟩ := DirectCrossingPairSeedsUnderInputs.uniform_bound r hr C ε hε
  refine ⟨pd, pp, ?_⟩
  intro hgeoD hgeoP
  obtain ⟨N₀, hN₀, h⟩ := h hgeoD hgeoP
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband G hG
  exact (DirectCrossingSeedFamilies.mass_bound G L r).trans
    (h N hN L hband G hG (DirectCrossingSeedFamilies.targets G L r)
      (fun _ _ _ hA ↦ (DirectCrossingSeedFamilies.mem_targets _ _ _ _ _).mp hA))

theorem uniform_extensions (r : ℕ) (hr : 2 ≤ r) (k : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ pd : DensePrimitiveTripleMassUnderInputs.Parameters,
      ∃ pp : FinitePairDeficitInputs.Parameters,
      DensePrimitiveTripleMassUnderInputs.Hypotheses pd →
      FinitePairDeficitInputs.Hypotheses pp (GeneralGraphHostCount.sizeCap (ε / 4096)) →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        ∀ F : Finset (Finset ℕ),
        (∀ T ∈ F, T ⊆ dyadicBlock N ∧ T.card = (2 + r) + k ∧
          ∃ D ∈ DirectCrossingSeedFamilies.families G L r, D ⊆ T) →
        (∑ T ∈ F, infiniteJointMoment L T) ≤ (N : ℝ) ^ (-5 / 3 + ε) := by
  obtain ⟨pd, pp, hs⟩ := uniform_seeds r hr C (ε / 2) (by positivity)
  obtain ⟨NR, hrp⟩ := UnorderedSeedMassPropagation.uniform_mass (2 + r) (by omega) k C (ε / 4) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (((2 + r) + k).factorial : ℝ)
    (-5 / 3 + 3 * ε / 4) (ε / 4) (by positivity)
  refine ⟨pd, pp, ?_⟩
  intro hgeoD hgeoP
  have hscale : (ε / 2) / 2048 = ε / 4096 := by ring
  obtain ⟨NS, _hNS, hs⟩ := hs hgeoD (by simpa only [hscale] using hgeoP)
  refine ⟨4 + NS + NR + NG + NF, by omega, ?_⟩
  intro N hN L hband G hG F hF
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hseed := hs N (by omega) L hband G hG
  have hprop := hrp N (by omega) L hL hband (DirectCrossingSeedFamilies.families G L r)
    (fun D hD ↦ ⟨(DirectCrossingSeedFamilies.family_data G L r D hD).1.trans hG,
      (DirectCrossingSeedFamilies.family_data G L r D hD).2.1⟩) F hF
  calc
    _ ≤ (((2 + r) + k).factorial : ℝ) * (N : ℝ) ^ (ε / 4) * (N : ℝ) ^ (-5 / 3 + ε / 2) :=
      hprop.trans (mul_le_mul_of_nonneg_left hseed
        (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hn.le _)))
    _ = (((2 + r) + k).factorial : ℝ) * (N : ℝ) ^ (-5 / 3 + 3 * ε / 4) := by
      rw [mul_assoc, ← Real.rpow_add hn]
      congr 2
      ring
    _ ≤ _ := by
      convert hf N (by omega) using 1
      congr 1
      ring

end PaperP1.DirectCrossingSeedFamiliesUnderInputs
