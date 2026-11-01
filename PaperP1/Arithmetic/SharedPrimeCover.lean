module

public import PaperP1.Arithmetic.ThreeBlockCoordinates

/-! # The covered ternary rows are exactly the actual shared-prime hyperedges -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SharedPrimeCover

open Finset PaperP1.Arithmetic PaperP1.ThreeBlockCoordinates PaperP1.ColoredPrimeConstraints
  PaperP1.CoverGraphResolution PaperP1.DefectivePredicate PaperP1.LargeOddKernel

local instance sharedPrimeCoverTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

def Shared (X : Fin 3 → ℕ) (L : ℕ) (p : ℕ) : Prop :=
  ∀ i : Fin 3, ∃ j : Fin (L + 1), p ∈ oddPrimeSupport (label X L (i, j))

theorem shared_iff_rows_surjective (X : Fin 3 → ℕ) (L H : ℕ) (p : LargePrime H) :
    Shared X L p.val ↔ ∀ i : Fin 3, ∃ j : Fin (L + 1), (i, j) ∈ rows X L H p := by
  constructor
  · intro h i
    obtain ⟨j, hj⟩ := h i
    have hne := mem_oddPrimeSupport_iff_parityVec_ne_zero.mp hj
    refine ⟨j, mem_rows.mpr ?_⟩
    rcases binary_eq_zero_or_one (data X L (i, j) p.val) with hzero | hone
    · exact False.elim (hne hzero)
    · exact hone
  · intro h i
    obtain ⟨j, hj⟩ := h i
    refine ⟨j, mem_oddPrimeSupport_iff_parityVec_ne_zero.mpr ?_⟩
    change data X L (i, j) p.val ≠ 0
    rw [mem_rows.mp hj]
    exact one_ne_zero

theorem rows_card_eq_three_iff_shared {X : Fin 3 → ℕ} {L H : ℕ}
    (hX : ∀ i, 1 ≤ X i) (hH : L + 1 ≤ H) (p : LargePrime H) :
    (rows X L H p).card = 3 ↔ Shared X L p.val := by
  rw [shared_iff_rows_surjective]
  constructor
  · intro hcard
    have himage : (rows X L H p).image Prod.fst = (univ : Finset (Fin 3)) := by
      apply eq_of_subset_of_card_le (subset_univ _)
      rw [card_image_of_injOn (row_color_injective hX hH p), hcard, card_univ, Fintype.card_fin]
    intro i
    have hi : i ∈ (rows X L H p).image Prod.fst := by rw [himage]; exact mem_univ _
    obtain ⟨v, hv, hvi⟩ := mem_image.mp hi
    refine ⟨v.2, ?_⟩
    have heq : (i, v.2) = v := Prod.ext hvi.symm rfl
    rw [heq]
    exact hv
  · intro h
    have himage : (rows X L H p).image Prod.fst = (univ : Finset (Fin 3)) := by
      apply eq_univ_of_forall
      intro i
      obtain ⟨j, hj⟩ := h i
      exact mem_image.mpr ⟨(i, j), hj, rfl⟩
    have hcard := card_image_le (s := rows X L H p) (f := Prod.fst)
    rw [himage, card_univ, Fintype.card_fin] at hcard
    exact le_antisymm (rows_card_le_three hX hH p) hcard

def CoversShared (X : Fin 3 → ℕ) (L H : ℕ) (D : Finset (Vertex L)) : Prop :=
  ∀ p : LargePrime H, Shared X L p.val → (rows X L H p ∩ D).Nonempty

theorem cover_iff_shared {X : Fin 3 → ℕ} {L H : ℕ} (hX : ∀ i, 1 ≤ X i) (hH : L + 1 ≤ H)
    (D : Finset (Vertex L)) : IsCover (rows X L H) D ↔ CoversShared X L H D := by
  have hbound := rows_card_le_three hX hH
  constructor
  · intro h p hp
    exact h p (by rw [(rows_card_eq_three_iff_shared hX hH p).mpr hp])
  · intro h p hp
    exact h p ((rows_card_eq_three_iff_shared hX hH p).mp (by have hb := hbound p; omega))

end PaperP1.SharedPrimeCover
