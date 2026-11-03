module

public import PaperP1.Combinatorics.PhysicalLabelSupportCount

/-! # Every member of a fixed short-support pool has bounded physical size -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PhysicalSupportPoolBudget

open Finset PaperP1.PhysicalLabelSupportCount PaperP1.ZeroSumFreeRepresentations

variable {V A : Type*} [Fintype V] [DecidableEq V] [AddCommGroup A] [DecidableEq A]

theorem member_card (ℓ : V → A) (S : Finset A) (d K : ℕ)
    (hK : ∀ a ∈ S, (fibre ℓ a).card ≤ K) (α : A) {D : Finset V}
    (hD : D ∈ supportPool ℓ S d α) : D.card ≤ d * K := by
  obtain ⟨j, hj, hDj⟩ := mem_biUnion.mp hD
  obtain ⟨hjp, hjd⟩ := mem_Icc.mp hj
  have hrep : D.image ℓ ∈ representations S j α := (mem_filter.mp hDj).2
  have hrepdata := mem_representations.mp hrep
  have hsub : D ⊆ preimage ℓ (D.image ℓ) := by
    intro v hv
    exact mem_filter.mpr ⟨mem_univ _, mem_image.mpr ⟨v, hv, rfl⟩⟩
  calc
    _ ≤ (preimage ℓ (D.image ℓ)).card := card_le_card hsub
    _ ≤ (D.image ℓ).card * K := preimage_card ℓ _ K (fun a ha ↦ hK a (hrepdata.1 ha))
    _ = j * K := by rw [hrepdata.2.1]
    _ ≤ _ := Nat.mul_le_mul_right K hjd

theorem inserted_member_card (ℓ : V → A) (S : Finset A) (d K : ℕ)
    (hK : ∀ a ∈ S, (fibre ℓ a).card ≤ K) (α : A) (v : V) {D : Finset V}
    (hD : D ∈ supportPool ℓ S d α) : (insert v D).card ≤ d * K + 1 :=
  (card_insert_le _ _).trans (Nat.add_le_add_right (member_card ℓ S d K hK α hD) 1)

end PaperP1.PhysicalSupportPoolBudget
