module

public import PaperP1.Asymptotics.ExpandedAsymmetricDenseMass
public import PaperP1.Asymptotics.AsymmetricSubsetComponents
public import PaperP1.Asymptotics.SubsetDenseNonalignedHosts

/-! # The actual asymmetric dense weighted sector with internal pinned-support confinement -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AsymmetricDenseMass

open Finset PaperP1.Model PaperP1.AsymmetricEvenLoss PaperP1.AsymmetricComponentHostData

local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem uniform_weight (C ε η : ℝ) (Dold Dcut : ℕ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H R : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → R ≤ Dold * (L + 1) →
      ∀ (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H), H ≤ Dcut * (L + 1) →
      ∀ old : ℕ → Finset ℕ,
      (∀ x ∈ dyadicBlock N, ∀ n ∈ old x, |(n : ℤ) - x| ≤ (R : ℤ)) →
      ∀ F : Finset (ℕ × ℕ), (∀ p ∈ F, p.1 ∈ dyadicBlock N ∧ p.2 ∈ dyadicBlock N) →
      (∀ p ∈ F, ¬CompressedTargetAlignment.Aligned Dold p.1 p.2 L) →
      (∀ p ∈ F, η * ((L + 1 : ℕ) : ℝ) ≤ (nontrivial p.1 p.2 L H R hnew hamb (old p.1)).card) →
      (∑ p ∈ F, (2 ^ loss H (old p.1) p.2 L : ℝ)) ≤ (N : ℝ) ^ (1 + ε) := by
  obtain ⟨N₀, hN₀, h⟩ := ExpandedAsymmetricDenseMass.uniform_weight 1 (by decide)
    C ε η Dold Dcut hε hη
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L H R hcrit hR hnew hamb hH old hold F hF hnon hdense
  have he : ExpandedAsymmetricSupportEnvelope.block N 1 = dyadicBlock N := by
    unfold ExpandedAsymmetricSupportEnvelope.block dyadicBlock
    congr 1
    omega
  exact h N hN L H R hcrit hR hnew hamb hH old (by simpa only [he] using hold) F
    (fun p hp ↦ ⟨ExpandedAsymmetricSupportEnvelope.dyadic_subset_block (by decide) (hF p hp).1,
      (hF p hp).2⟩) hnon hdense

end PaperP1.AsymmetricDenseMass
