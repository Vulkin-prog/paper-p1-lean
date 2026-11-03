module

public import PaperP1.Affine.RelationProjectionRank
public import PaperP1.Affine.RetainedNullity

/-! # The actual deletion nullity loss is monotone under adjoining blocks -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RelationLossMonotonicity

open Finset PaperP1.Affine PaperP1.RelationProjectionRank

variable {U κ : Type*} [AddCommGroup U] [Module 𝔽₂ U] [DecidableEq κ]
variable (S : κ → Submodule 𝔽₂ U) [∀ i, Fintype (S i)]

theorem mono (A B : Finset κ) (hAB : A ⊆ B) (x : κ) (hx : x ∈ A) : loss S A x ≤ loss S B x := by
  let ia : A := ⟨x, hx⟩
  let ib : B := ⟨x, hAB hx⟩
  have hrange : LinearMap.range (PrimitiveCoordinateProjection.projection S A ia) ≤
      LinearMap.range (PrimitiveCoordinateProjection.projection S B ib) := by
    rintro v ⟨r, rfl⟩
    refine ⟨subfamilyKernelExtend S hAB r, ?_⟩
    change (if h : x ∈ A then r.val ⟨x, h⟩ else 0) = r.val ⟨x, hx⟩
    rw [dite_eq_left hx]
  rw [loss_eq_dimension S A ia, loss_eq_dimension S B ib]
  exact Submodule.finrank_mono hrange

theorem pair_loss (e : Finset κ) (he : e.card = 2) (x : κ) (hx : x ∈ e) :
    loss S e x = relativeNullityOn S e := by
  have hzero := RetainedNullity.nullity_card_le_one S (e.erase x) (by rw [card_erase_of_mem hx, he])
  rw [loss, hzero, Nat.sub_zero]

end PaperP1.RelationLossMonotonicity
