module

public import PaperP1.Affine.CanonicalIndexTransport

/-! # Turning a part of a finite subtype into an actual finite index set -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FinitePartImage

open Finset PaperP1.Affine

variable {κ : Type*} [DecidableEq κ] {B : Finset κ}

def image (C : Finset B) : Finset κ := C.image (fun i : B ↦ i.val)

def equiv (C : Finset B) : C ≃ image C := Equiv.ofBijective
  (fun i ↦ ⟨i.val.val, mem_image.mpr ⟨i.val, i.property, rfl⟩⟩) (by
    constructor
    · intro i j h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun k : image C ↦ k.val) h
    · intro k
      obtain ⟨i, hi, hik⟩ := mem_image.mp k.property
      refine ⟨⟨i, hi⟩, ?_⟩
      exact Subtype.ext hik)

theorem card_image (C : Finset B) : (image C).card = C.card :=
  card_image_of_injective C Subtype.val_injective

theorem image_subset (C : Finset B) : image C ⊆ B := by
  intro k hk
  obtain ⟨i, _, rfl⟩ := mem_image.mp hk
  exact i.property

theorem image_nonempty {C : Finset B} (hC : C.Nonempty) : (image C).Nonempty := by
  obtain ⟨i, hi⟩ := hC
  exact ⟨i.val, mem_image.mpr ⟨i, hi, rfl⟩⟩

theorem prod_equiv (C : Finset B) {M : Type*} [CommMonoid M] (f : κ → M) :
    (∏ i : C, f i.val.val) = ∏ k : image C, f k.val :=
  (equiv C).prod_comp (fun k : image C ↦ f k.val)

variable {U : Type*} [AddCommGroup U] [Module 𝔽₂ U]
variable (S : κ → Submodule 𝔽₂ U)

theorem connected_image (C : Finset B) [Nonempty C]
    (hconnected : canonicalRelationPartition (fun i : C ↦ S i.val.val) = ⊤) :
    canonicalRelationPartition (fun k : image C ↦ S k.val) = ⊤ := by
  let : Nonempty (image C) := ⟨equiv C (Classical.choice ‹Nonempty C›)⟩
  apply CanonicalIndexTransport.connected_reindex (fun k : image C ↦ S k.val) (equiv C)
  exact hconnected

theorem nullity_image (C : Finset B) [∀ k, Fintype (S k)] :
    relativeNullityOn (fun i : B ↦ S i.val) C = relativeNullityOn S (image C) :=
  CanonicalIndexTransport.nullity_reindex (fun k : image C ↦ S k.val) (equiv C)

end PaperP1.FinitePartImage
