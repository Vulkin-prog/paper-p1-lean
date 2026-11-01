module

public import PaperP1.Model.ConnectedWindowFamilies
public import PaperP1.Arithmetic.BlockSupportProjection

/-! # Actual original-window relations with many nonzero effective projections -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SeveralWindowProjections

open Finset PaperP1.Arithmetic

def Relation {r : ℕ} (L : ℕ) (n : Fin r → ℕ) (s : ℕ) : Prop :=
  ∃ u : Fin r → (ℕ →₀ F₂), (∀ i, u i ∈ squareClassSpace (n i) L) ∧
    (∑ i, u i) = 0 ∧ s ≤ (univ.filter fun i ↦ u i ≠ 0).card

def tuples (G : Finset ℕ) (L r s : ℕ) : Finset (Fin r → ℕ) := by
  classical
  exact (Fintype.piFinset fun _ : Fin r ↦ G).filter fun n ↦ Function.Injective n ∧ Relation L n s

theorem tuples_eq (G : Finset ℕ) (L r s : ℕ) :
    tuples G L r s = PaperP1.BlockSupportProjection.population G (PaperP1.ConnectedWindowFamilies.blocks L r) s := by
  classical
  ext n
  simp only [tuples, PaperP1.BlockSupportProjection.population, mem_filter]
  constructor
  · rintro ⟨hnG, hinj, u, hu, hsum, hsize⟩
    refine ⟨hnG, hinj, u, ?_, hsum, hsize⟩
    intro i
    simpa only [PaperP1.ConnectedWindowFamilies.blocks, PaperP1.NormalizedWindowSets.space_values] using hu i
  · rintro ⟨hnG, hinj, u, hu, hsum, hsize⟩
    refine ⟨hnG, hinj, u, ?_, hsum, hsize⟩
    intro i
    simpa only [PaperP1.ConnectedWindowFamilies.blocks, PaperP1.NormalizedWindowSets.space_values] using hu i

end PaperP1.SeveralWindowProjections
