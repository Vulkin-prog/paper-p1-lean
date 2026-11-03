module

public import PaperP1.Asymptotics.TwoTargetJointMassUnderInputs
public import PaperP1.Asymptotics.DependentPairJointMassUnderInputs

/-! # Dense nonaligned or weakly aligned two-pair crossings have actual seed mass N⁻⁵ᐟ³ -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DenseAdmissiblePairSeedsUnderInputs

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.SubspaceFamilyRank PaperP1.TwoTargetPrimitiveData

theorem uniform_bound (C η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ θ : ℝ, 0 < θ ∧ ∃ pd : DensePrimitiveTripleMassUnderInputs.Parameters,
      ∃ pp : FinitePairDeficitInputs.Parameters,
      (DensePrimitiveTripleMassUnderInputs.Hypotheses pd →
      FinitePairDeficitInputs.Hypotheses pp (GeneralGraphHostCount.sizeCap (ε / 2048)) →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        ∀ F : Finset ℕ → Finset (ℕ × ℕ),
        (∀ e ∈ DependentFamilySeeds.dependentFamilies G L 2, ∀ p ∈ F e,
          p.1 ∈ dyadicBlock N ∧ p.2 ∈ dyadicBlock N ∧ p.1 ≠ p.2 ∧ p.1 ∉ e ∧ p.2 ∉ e) →
        (∀ e ∈ DependentFamilySeeds.dependentFamilies G L 2, ∀ p ∈ F e,
          ¬ CompressedTargetAlignment.Aligned 1 p.1 p.2 L ∨
          (Module.finrank F₂ ↥(squareClassSpace p.1 L ⊓ squareClassSpace p.2 L) : ℝ) ≤ θ * L) →
        (∀ e ∈ DependentFamilySeeds.dependentFamilies G L 2, ∀ p ∈ F e, ∀ B : Finset ℕ,
          B ⊂ {p.1, p.2} → Disjoint (sourceSpace e L) (span (fun x ↦ squareClassSpace x L) B)) →
        (∀ e ∈ DependentFamilySeeds.dependentFamilies G L 2, ∀ p ∈ F e,
          η * L ≤ (Module.finrank F₂ ↥(sourceSpace e L ⊓
            span (fun x ↦ squareClassSpace x L) {p.1, p.2}) : ℝ)) →
        (∑ e ∈ DependentFamilySeeds.dependentFamilies G L 2,
          ∑ p ∈ F e, infiniteJointMoment L (TwoTargetFamilyCover.family e p)) ≤ (N : ℝ) ^ (-5 / 3 + ε)) := by
  obtain ⟨θ, hθ, pd, hd⟩ := TwoTargetJointMassUnderInputs.uniform_joint 2 C η (ε / 2) hη (by positivity)
  obtain ⟨pp, hp⟩ := DependentPairJointMassUnderInputs.uniform_bound C (ε / 2) (by positivity)
  refine ⟨θ, hθ, pd, pp, ?_⟩
  intro hgeoD hgeoP
  obtain ⟨ND, _hND, hd⟩ := hd hgeoD
  have hscale : (ε / 2) / 1024 = ε / 2048 := by ring
  obtain ⟨NP, _hNP, hp⟩ := hp (by simpa only [hscale] using hgeoP)
  refine ⟨4 + ND + NP, by omega, ?_⟩
  intro N hN L hband G hG F hF hadmiss hproper hdense
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpair := hp N (by omega) L hband G hG
  have hcell (e : Finset ℕ) (he : e ∈ DependentFamilySeeds.dependentFamilies G L 2) :
      (∑ p ∈ F e, infiniteJointMoment L (TwoTargetFamilyCover.family e p)) ≤
        infiniteJointMoment L e * (N : ℝ) ^ (-1 + ε / 2) := by
    obtain ⟨heG, _hdep⟩ := mem_filter.mp he
    obtain ⟨hesub, hecard⟩ := mem_powersetCard.mp heG
    exact hd N (by omega) L hband e hecard (hesub.trans hG) (F e)
      (hF e he) (hadmiss e he) (hproper e he) (hdense e he)
  calc
    _ ≤ ∑ e ∈ DependentFamilySeeds.dependentFamilies G L 2,
        infiniteJointMoment L e * (N : ℝ) ^ (-1 + ε / 2) := sum_le_sum hcell
    _ = (N : ℝ) ^ (-1 + ε / 2) *
        ∑ e ∈ DependentFamilySeeds.dependentFamilies G L 2, infiniteJointMoment L e := by
      rw [← sum_mul, mul_comm]
    _ ≤ (N : ℝ) ^ (-1 + ε / 2) * (N : ℝ) ^ (-2 / 3 + ε / 2) :=
      mul_le_mul_of_nonneg_left hpair (Real.rpow_nonneg hn.le _)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring

end PaperP1.DenseAdmissiblePairSeedsUnderInputs
