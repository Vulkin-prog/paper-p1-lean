module

public import PaperP1.Algebra.ProjectedPreimageRank
public import PaperP1.Arithmetic.AsymmetricEvenLoss

/-! # Genuine effective-space intersections are bounded by the literal asymmetric loss

The old space may keep its even-selection constraint and all prime
coordinates. Forgetting small primes and dropping the old parity condition
only enlarges the preimage budget. No new-window injectivity is needed.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AsymmetricIntersectionTransport

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.AsymmetricEvenLoss

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def projection (H : ℕ) : (ℕ →₀ F₂) →ₗ[F₂] (ℕ →₀ F₂) where
  toFun v := v.filter fun p ↦ H < p
  map_add' u v := by
    ext p
    simp only [Finsupp.filter_apply, Finsupp.add_apply]
    split_ifs <;> rfl
  map_smul' c v := by
    ext p
    by_cases hp : H < p <;> simp [hp]

theorem old_image_le (H : ℕ) (U : Finset ℕ) :
    (FiniteEvenSquareClasses.space U).map (projection H) ≤ oldSpace H U := by
  intro v hv
  obtain ⟨z, hz, rfl⟩ := hv
  obtain ⟨w, _heven, he⟩ := (EvenImage.mem_image_iff (FiniteEvenSquareClasses.data U) z).mp hz
  rw [← he, EvenImage.combination_apply, map_sum]
  apply Submodule.sum_mem
  intro n _hn
  rw [map_smul]
  exact Submodule.smul_mem _ _ (old_mem n.property)

theorem new_map_eq (H z L : ℕ) :
    EvenImage.evenMap (newData H z L) =
      (projection H).comp (EvenImage.evenMap (fun i : Fin (L + 1) ↦ parityVec (startCompleteVertexLabel z L i))) := by
  apply LinearMap.ext
  intro w
  change EvenImage.combination (newData H z L) w.val = projection H
    (EvenImage.combination (fun i : Fin (L + 1) ↦ parityVec (startCompleteVertexLabel z L i)) w.val)
  rw [EvenImage.combination_apply, EvenImage.combination_apply, map_sum]
  simp only [map_smul]
  rfl

theorem intersection_le_loss (H : ℕ) (U : Finset ℕ) (z L : ℕ) :
    Module.finrank F₂ ↥(FiniteEvenSquareClasses.space U ⊓ squareClassSpace z L) ≤ loss H U z L := by
  have hh := ProjectedPreimageRank.intersection_le
    (EvenImage.evenMap (fun i : Fin (L + 1) ↦ parityVec (startCompleteVertexLabel z L i)))
    (projection H) (FiniteEvenSquareClasses.space U) (oldSpace H U) (old_image_le H U)
  rw [← new_map_eq, ← EvenImage.image, ← NormalizedWindowSets.squareClassSpace_eq_evenImage, inf_comm] at hh
  exact hh

end PaperP1.AsymmetricIntersectionTransport
