module

public import PaperP1.Asymptotics.DirectCrossingFamiliesUnderInputs
public import PaperP1.Asymptotics.DependentPairJointMassUnderInputs

/-! # The complete direct-crossing seed alternative of main15.10 has joint mass N⁻⁵ᐟ³ -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DirectCrossingPairSeedsUnderInputs

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.SubspaceFamilyRank

theorem uniform_bound (r : ℕ) (hr : 2 ≤ r) (C ε : ℝ) (hε : 0 < ε) :
    ∃ pd : DensePrimitiveTripleMassUnderInputs.Parameters,
    ∃ pp : FinitePairDeficitInputs.Parameters,
      (DensePrimitiveTripleMassUnderInputs.Hypotheses pd →
      FinitePairDeficitInputs.Hypotheses pp (GeneralGraphHostCount.sizeCap (ε / 2048)) →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        ∀ F : Finset ℕ → Finset (Finset ℕ),
        (∀ e ∈ DependentFamilySeeds.dependentFamilies G L 2, ∀ A ∈ F e,
          A ⊆ G \ e ∧ A.card = r ∧ runRelativeNullity L A = 0 ∧
          span (fun x ↦ squareClassSpace x L) e ⊓ span (fun x ↦ squareClassSpace x L) A ≠ ⊥ ∧
          ∀ B : Finset ℕ, B ⊂ A →
            Disjoint (span (fun x ↦ squareClassSpace x L) e) (span (fun x ↦ squareClassSpace x L) B)) →
        (∑ e ∈ DependentFamilySeeds.dependentFamilies G L 2,
          ∑ A ∈ F e, infiniteJointMoment L (e ∪ A)) ≤ (N : ℝ) ^ (-5 / 3 + ε)) := by
  obtain ⟨pd, hd⟩ := DirectCrossingFamiliesUnderInputs.uniform_families r 2 hr C (ε / 2) (by positivity)
  obtain ⟨pp, hp⟩ := DependentPairJointMassUnderInputs.uniform_bound C (ε / 2) (by positivity)
  refine ⟨pd, pp, ?_⟩
  intro hgeoD hgeoP
  obtain ⟨ND, _hND, hd⟩ := hd hgeoD
  have hscale : (ε / 2) / 1024 = ε / 2048 := by ring
  obtain ⟨NP, _hNP, hp⟩ := hp (by simpa only [hscale] using hgeoP)
  refine ⟨4 + ND + NP, by omega, ?_⟩
  intro N hN L hband G hG F hF
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpair := hp N (by omega) L hband G hG
  have hcell (e : Finset ℕ) (he : e ∈ DependentFamilySeeds.dependentFamilies G L 2) :
      (∑ A ∈ F e, infiniteJointMoment L (e ∪ A)) ≤
        infiniteJointMoment L e * (N : ℝ) ^ (-1 + ε / 2) := by
    obtain ⟨heG, _hdep⟩ := mem_filter.mp he
    obtain ⟨hesub, hecard⟩ := mem_powersetCard.mp heG
    exact hd N (by omega) L hband e hecard (hesub.trans hG) G hG (F e) (hF e he)
  calc
    _ ≤ ∑ e ∈ DependentFamilySeeds.dependentFamilies G L 2,
        infiniteJointMoment L e * (N : ℝ) ^ (-1 + ε / 2) := sum_le_sum hcell
    _ = (N : ℝ) ^ (-1 + ε / 2) *
        ∑ e ∈ DependentFamilySeeds.dependentFamilies G L 2, infiniteJointMoment L e := by
      rw [← sum_mul, mul_comm]
    _ ≤ (N : ℝ) ^ (-1 + ε / 2) * (N : ℝ) ^ (-2 / 3 + ε / 2) :=
      mul_le_mul_of_nonneg_left hpair (Real.rpow_nonneg hn.le _)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring

end PaperP1.DirectCrossingPairSeedsUnderInputs
