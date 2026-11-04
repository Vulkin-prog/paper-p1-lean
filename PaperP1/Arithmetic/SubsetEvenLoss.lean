module

public import PaperP1.Arithmetic.AsymmetricIntersectionTransport

/-! # Actual even-selection loss on a prescribed finite new value set

Only actual new values contribute to the domain dimension. Old parity is
dropped and small-prime coordinates are forgotten on both sides.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SubsetEvenLoss

open PaperP1.Arithmetic PaperP1.Affine PaperP1.AsymmetricEvenLoss

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def data (H : ℕ) (V : Finset ℕ) : V → ℕ →₀ F₂ := fun n ↦ largeParity H n.val

def loss (H : ℕ) (U V : Finset ℕ) : ℕ :=
  Module.finrank F₂ ((oldSpace H U).comap (EvenImage.evenMap (data H V)))

theorem new_map_eq (H : ℕ) (V : Finset ℕ) :
    EvenImage.evenMap (data H V) =
      (AsymmetricIntersectionTransport.projection H).comp (EvenImage.evenMap (FiniteEvenSquareClasses.data V)) := by
  apply LinearMap.ext
  intro w
  change EvenImage.combination (data H V) w.val = AsymmetricIntersectionTransport.projection H
    (EvenImage.combination (FiniteEvenSquareClasses.data V) w.val)
  rw [EvenImage.combination_apply, EvenImage.combination_apply, map_sum]
  simp only [map_smul]
  rfl

theorem intersection_le_loss (H : ℕ) (U V : Finset ℕ) :
    Module.finrank F₂ ↥(FiniteEvenSquareClasses.space U ⊓ FiniteEvenSquareClasses.space V) ≤ loss H U V := by
  have hh := ProjectedPreimageRank.intersection_le (EvenImage.evenMap (FiniteEvenSquareClasses.data V))
    (AsymmetricIntersectionTransport.projection H) (FiniteEvenSquareClasses.space U) (oldSpace H U)
    (AsymmetricIntersectionTransport.old_image_le H U)
  rw [← new_map_eq, ← EvenImage.image, ← FiniteEvenSquareClasses.space, inf_comm] at hh
  exact hh

theorem loss_le_card (H : ℕ) (U V : Finset ℕ) : loss H U V ≤ V.card - 1 := by
  have hh : loss H U V ≤ Module.finrank F₂ (LinearMap.ker (EvenSupportRank.sumMap F₂ V)) := Submodule.finrank_le _
  rw [EvenSupportRank.kernel_sum_finrank, Fintype.card_coe] at hh
  exact hh

end PaperP1.SubsetEvenLoss
