module

public import PaperP1.Affine.PrivateCoreMoments

/-! # Companion T19.8: every conclusion of private-rank peeling -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrivateRankPeelingTheorem

open Finset PaperP1.Affine PaperP1.SubspaceFamilyRank PaperP1.PrivateRankCore PaperP1.PrivateCoreMoments

variable {V ι : Type*} [AddCommGroup V] [Module 𝔽₂ V] [Fintype V] [DecidableEq ι]
variable (S : ι → Submodule 𝔽₂ (V →ₗ[𝔽₂] 𝔽₂)) [∀ i, Fintype (S i)]

/-- The moments are the original uniform affine-event moments, with arbitrary compatible local prescriptions. -/
theorem companion_T19_8 (A : Finset ι) (a : ι → V) (L t : ℕ) (ht : 1 ≤ t) (htL : t ≤ L)
    (hL : ∀ i ∈ A, Module.finrank 𝔽₂ (S i) = L)
    (hcompatible : ∃ b : V, ∀ i ∈ A, effectiveEvent (S i) (a i) b) :
    ∃ B ⊆ A, (A.card : ℝ) - rank S A / (t : ℝ) ≤ B.card ∧ rank S B ≤ rank S A ∧
      (∀ i ∈ B, privateRank S B i < t) ∧ ComponentMassConclusion S A B a L t ∧ DenseConclusion S A B L t := by
  obtain ⟨B, hBA, hsize, hrank, hstop, hdense⟩ := exists_core S A L t (by omega) htL hL
  exact ⟨B, hBA, hsize, hrank, hstop, component_mass_bounds S A B hBA a L t hL hstop hcompatible, hdense⟩

end PaperP1.PrivateRankPeelingTheorem
