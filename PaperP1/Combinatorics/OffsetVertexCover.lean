module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Find

/-! # The actual minimum vertex cover of a finite ternary offset population -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OffsetVertexCover

open Finset

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def Covers (S : Finset (Fin 3 → ℤ)) (D : Finset (Fin 3 × ℤ)) : Prop :=
  ∀ u ∈ S, ∃ i : Fin 3, (i, u i) ∈ D

def firstCover (S : Finset (Fin 3 → ℤ)) : Finset (Fin 3 × ℤ) := S.image fun u ↦ (0, u 0)

theorem first_covers (S : Finset (Fin 3 → ℤ)) : Covers S (firstCover S) := by
  intro u hu
  exact ⟨0, mem_image.mpr ⟨u, hu, rfl⟩⟩

theorem exists_cover (S : Finset (Fin 3 → ℤ)) :
    ∃ n : ℕ, ∃ D : Finset (Fin 3 × ℤ), D.card = n ∧ Covers S D :=
  ⟨(firstCover S).card, firstCover S, rfl, first_covers S⟩

def minimum (S : Finset (Fin 3 → ℤ)) : ℕ := Nat.find (exists_cover S)

theorem minimum_realized (S : Finset (Fin 3 → ℤ)) :
    ∃ D : Finset (Fin 3 × ℤ), D.card = minimum S ∧ Covers S D := Nat.find_spec (exists_cover S)

theorem minimum_le_card {S : Finset (Fin 3 → ℤ)} {D : Finset (Fin 3 × ℤ)} (hD : Covers S D) :
    minimum S ≤ D.card := Nat.find_min' (exists_cover S) ⟨D, rfl, hD⟩

theorem minimum_le_supports (S : Finset (Fin 3 → ℤ)) : minimum S ≤ S.card :=
  (minimum_le_card (first_covers S)).trans card_image_le

end PaperP1.OffsetVertexCover
