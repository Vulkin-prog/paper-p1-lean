module

public import PaperP1.Model.RunFamilyEnumeration
public import PaperP1.Asymptotics.PositionedMassPropagation

/-! # Actual unordered seed masses propagate to every fixed larger family size -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UnorderedSeedMassPropagation

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.RunFamilyEnumeration

/-- No compatibility, regularity or positivity assumption is made on the seed
masses. Their actual zero masses are retained throughout the propagation. -/
theorem uniform_mass (s : ℕ) (hs : 1 ≤ s) (k : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, 0 < L →
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ F : Finset (Finset ℕ), (∀ D ∈ F, D ⊆ dyadicBlock N ∧ D.card = s) →
      ∀ T : Finset (Finset ℕ),
        (∀ I ∈ T, I ⊆ dyadicBlock N ∧ I.card = s + k ∧ ∃ D ∈ F, D ⊆ I) →
        (∑ I ∈ T, infiniteJointMoment L I) ≤
          ((s + k).factorial : ℝ) * (N : ℝ) ^ ε * ∑ D ∈ F, infiniteJointMoment L D := by
  obtain ⟨N₀, hN₀⟩ := PositionedMassPropagation.all_positions s hs k C ε hε
  refine ⟨N₀, ?_⟩
  intro N hN L hL hband F hF T hT
  have hsub : tuples T (s + k) ⊆ TuplePositions.allPositions (dyadicBlock N) (tuples F s) k := by
    intro x hx
    obtain ⟨I, hI, rfl⟩ := mem_image.mp hx
    obtain ⟨D, hD, hDI⟩ := (hT I hI).2.2
    exact seeded_tuple_mem (dyadicBlock N) F hF I (hT I hI).1 (hT I hI).2.1 hD hDI
  rw [← sum_tuples_joint hL T (fun I hI ↦ (hT I hI).2.1),
    ← sum_tuples_joint hL F (fun D hD ↦ (hF D hD).2)]
  exact (sum_le_sum_of_subset_of_nonneg hsub
    (fun x _ _ ↦ PrescribedTupleMass.joint_nonneg (fun _ ↦ Affine.startRhs L) x)).trans
      (hN₀ N hN L hband (fun _ ↦ Affine.startRhs L) (tuples F s)
        (tuples_coordinates (dyadicBlock N) F hF))

end PaperP1.UnorderedSeedMassPropagation
