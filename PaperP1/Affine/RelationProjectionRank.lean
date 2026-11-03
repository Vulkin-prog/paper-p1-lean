module

public import PaperP1.Affine.PrimitiveCoordinateProjection
public import PaperP1.Affine.PrivateNullity

/-! # The exact effective relation projection rank equals the deletion nullity loss -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RelationProjectionRank

open Finset PaperP1.Affine

local instance projectionRankPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {U κ : Type*} [AddCommGroup U] [Module 𝔽₂ U] [DecidableEq κ]
variable (S : κ → Submodule 𝔽₂ U) [∀ i, Fintype (S i)]

def loss (I : Finset κ) (i : κ) : ℕ := relativeNullityOn S I - relativeNullityOn S (I.erase i)

theorem kernel_finrank (I : Finset κ) (i : I) :
    Module.finrank 𝔽₂ (LinearMap.ker (PaperP1.PrimitiveCoordinateProjection.projection S I i)) =
      relativeNullityOn S (I.erase i.val) := by
  classical
  let : Fintype (RelationOn S I) := Fintype.ofFinite _
  let : Fintype (LinearMap.ker (PaperP1.PrimitiveCoordinateProjection.projection S I i)) :=
    Fintype.ofFinite _
  have hcard : Fintype.card (LinearMap.ker
      (PaperP1.PrimitiveCoordinateProjection.projection S I i)) = (missedRelations S I i).card := by
    let e : LinearMap.ker (PaperP1.PrimitiveCoordinateProjection.projection S I i) ≃
        {r : RelationOn S I // r.val i = 0} :=
      { toFun := fun r ↦ ⟨r.val, r.property⟩
        invFun := fun r ↦ ⟨r.val, r.property⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    calc
      _ = Fintype.card {r : RelationOn S I // r.val i = 0} := Fintype.card_congr e
      _ = _ := by simpa only [missedRelations] using
        (Fintype.card_subtype (fun r : RelationOn S I ↦ r.val i = 0))
  have hpow : Fintype.card (LinearMap.ker
      (PaperP1.PrimitiveCoordinateProjection.projection S I i)) =
      2 ^ Module.finrank 𝔽₂ (LinearMap.ker
        (PaperP1.PrimitiveCoordinateProjection.projection S I i)) :=
    card_eq_two_pow_finrank (V := LinearMap.ker
      (PaperP1.PrimitiveCoordinateProjection.projection S I i))
  apply Nat.pow_right_injective (by norm_num : 2 ≤ (2 : ℕ))
  exact hpow.symm.trans (hcard.trans (card_missedRelations S I i))

theorem dimension_identity (I : Finset κ) (i : I) :
    Module.finrank 𝔽₂ (LinearMap.range (PaperP1.PrimitiveCoordinateProjection.projection S I i)) +
      relativeNullityOn S (I.erase i.val) = relativeNullityOn S I := by
  have h := (PaperP1.PrimitiveCoordinateProjection.projection S I i).finrank_range_add_finrank_ker
  rw [kernel_finrank] at h
  exact h

theorem loss_eq_dimension (I : Finset κ) (i : I) :
    loss S I i.val = Module.finrank 𝔽₂
      (LinearMap.range (PaperP1.PrimitiveCoordinateProjection.projection S I i)) := by
  have h := dimension_identity S I i
  unfold loss
  omega

theorem erase_add_loss (I : Finset κ) (i : κ) :
    relativeNullityOn S (I.erase i) + loss S I i = relativeNullityOn S I := by
  have hmono := relativeNullityOn_mono S (erase_subset i I)
  unfold loss
  omega

end PaperP1.RelationProjectionRank
