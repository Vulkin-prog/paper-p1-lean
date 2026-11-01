module

public import PaperP1.Affine.IndependentRows

/-! # Exact affine mass when the only row relations are zero and one fixed word -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.Affine

open Finset

variable {V β : Type*} [AddCommGroup V] [Module 𝔽₂ V] [Fintype V]
variable [Fintype β] [DecidableEq β]

omit [Fintype V] in
theorem relationSignedSum_eq_one_add_sign (A : V →ₗ[𝔽₂] (β → 𝔽₂)) (b u : β → 𝔽₂)
    (hu : u ≠ 0) (hrel : relationMap A u = 0)
    (honly : ∀ v, relationMap A v = 0 → v = 0 ∨ v = u) :
    relationSignedSum A b = 1 + binarySign (dotProduct u b) := by
  classical
  unfold relationSignedSum
  calc
    _ = ∑ v ∈ ({0, u} : Finset (β → 𝔽₂)),
        if relationMap A v = 0 then binarySign (dotProduct v b) else 0 := by
      symm
      apply sum_subset (subset_univ _)
      intro v _ hv
      have hnot : relationMap A v ≠ 0 := by
        intro hz
        exact hv (by rcases honly v hz with h | h <;> simp [h])
      simp only [hnot, ite_false]
    _ = _ := by
      rw [sum_pair hu.symm]
      simp only [map_zero, ite_true, hrel, zero_dotProduct, binarySign_zero]

theorem uniformSolutionMass_eq_one_add_sign (A : V →ₗ[𝔽₂] (β → 𝔽₂)) (b u : β → 𝔽₂)
    (hu : u ≠ 0) (hrel : relationMap A u = 0)
    (honly : ∀ v, relationMap A v = 0 → v = 0 ∨ v = u) :
    uniformSolutionMass A b = (Fintype.card (β → 𝔽₂) : ℝ)⁻¹ *
      (1 + (binarySign (dotProduct u b) : ℝ)) := by
  classical
  have hid := affineFiber_fourier_identity A b
  rw [relationSignedSum_eq_one_add_sign A b u hu hrel honly] at hid
  have hr : (Fintype.card (β → 𝔽₂) : ℝ) *
      ((univ.filter fun x : V ↦ A x = b).card : ℝ) =
        Fintype.card V * (1 + (binarySign (dotProduct u b) : ℝ)) := by exact_mod_cast hid
  have hmass : uniformSolutionMass A b =
      ((univ.filter fun x : V ↦ A x = b).card : ℝ) / Fintype.card V := by
    rw [uniformSolutionMass_eq_card_ratio]
    congr 1
    apply congrArg (fun n : ℕ ↦ (n : ℝ))
    refine @Fintype.card_of_subtype V (fun x : V ↦ x ∈ solutionSet A b)
      (univ.filter fun x : V ↦ A x = b) ?_ (realSolutionFintype A b)
    intro x
    simp only [mem_filter, mem_univ, true_and, mem_solutionSet_iff]
  rw [hmass]
  have hV : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hW : (Fintype.card (β → 𝔽₂) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp [hV, hW]
  nlinarith [hr]

end PaperP1.Affine
