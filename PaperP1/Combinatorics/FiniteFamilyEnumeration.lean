module

public import PaperP1.Arithmetic.EffectiveExposure

/-! # Actual unordered finite families are images of injective enumerations -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteFamilyEnumeration

open Finset

def tupleSet {r : ℕ} (n : Fin r → ℕ) : Finset ℕ := univ.image n

def enumeration {r : ℕ} (I : Finset ℕ) (hI : I.card = r) : Fin r ≃ I :=
  (Fintype.equivFinOfCardEq (by simpa only [Fintype.card_coe] using hI)).symm

def centres {r : ℕ} (I : Finset ℕ) (hI : I.card = r) : Fin r → ℕ := fun i ↦ (enumeration I hI i).val

theorem centres_injective {r : ℕ} (I : Finset ℕ) (hI : I.card = r) : Function.Injective (centres I hI) := by
  intro i j hij
  exact (enumeration I hI).injective (Subtype.ext hij)

theorem centres_mem {r : ℕ} (G I : Finset ℕ) (hI : I.card = r) (hIG : I ⊆ G) :
    ∀ i, centres I hI i ∈ G := fun i ↦ hIG (enumeration I hI i).property

theorem centres_tupleSet {r : ℕ} (I : Finset ℕ) (hI : I.card = r) : tupleSet (centres I hI) = I := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, _, rfl⟩ := mem_image.mp hx
    exact (enumeration I hI i).property
  · intro hx
    obtain ⟨i, hi⟩ := (enumeration I hI).surjective ⟨x, hx⟩
    exact mem_image.mpr ⟨i, mem_univ _, congrArg Subtype.val hi⟩

theorem family_count {r : ℕ} (F : Finset (Finset ℕ)) (P : Finset (Fin r → ℕ))
    (hcover : ∀ I ∈ F, ∃ n ∈ P, tupleSet n = I) : F.card ≤ P.card := by
  have hsub : F ⊆ P.image tupleSet := by
    intro I hI
    exact mem_image.mpr (hcover I hI)
  exact (card_le_card hsub).trans card_image_le

end PaperP1.FiniteFamilyEnumeration
