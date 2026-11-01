module

public import PaperP1.Algebra.DotTranspose
public import PaperP1.Affine.StartBoundaryRange

/-! # Injective coordinate selection preserves the complete even boundary -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SelectedBoundary

open Finset PaperP1.Affine PaperP1.DotTranspose

local instance selectedBoundaryDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def extend {α β : Type*} [Fintype α] (g : α → β) : (α → 𝔽₂) →ₗ[𝔽₂] (β → 𝔽₂) :=
  Fintype.linearCombination 𝔽₂ (fun i ↦ Pi.single (g i) 1)

theorem extend_single {α β : Type*} [Fintype α] (g : α → β) (i : α) :
    extend g (Pi.single i 1) = Pi.single (g i) 1 := by
  simp [extend, Fintype.linearCombination_apply, Pi.single_apply]

theorem extend_apply_image {α β : Type*} [Fintype α] (g : α → β) (hg : Function.Injective g)
    (w : α → 𝔽₂) (i : α) : extend g w (g i) = w i := by
  simp [extend, Fintype.linearCombination_apply, Finset.sum_apply, Pi.single_apply, hg.eq_iff]

theorem extend_injective {α β : Type*} [Fintype α] (g : α → β) (hg : Function.Injective g) :
    Function.Injective (extend g) := by
  intro w v hwv
  funext i
  have h := congrFun hwv (g i)
  simpa only [extend_apply_image g hg] using h

theorem sum_extend {α β : Type*} [Fintype α] [Fintype β] (g : α → β) (w : α → 𝔽₂) :
    (∑ j, extend g w j) = ∑ i, w i := by
  simp only [extend, Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [sum_comm]
  simp only [← mul_sum, Fintype.sum_pi_single', mul_one]

def evenExtend {k L : ℕ} (g : Fin (k + 1) → Fin (L + 1)) :
    LinearMap.ker (startVertexSum k) →ₗ[𝔽₂] LinearMap.ker (startVertexSum L) :=
  ((extend g).comp (LinearMap.ker (startVertexSum k)).subtype).codRestrict
    (LinearMap.ker (startVertexSum L)) (fun w ↦ by
      change (∑ j, extend g w.val j) = 0
      rw [sum_extend]
      exact w.property)

theorem evenExtend_injective {k L : ℕ} (g : Fin (k + 1) → Fin (L + 1)) (hg : Function.Injective g) :
    Function.Injective (evenExtend g) := by
  intro w v hwv
  apply Subtype.ext
  apply extend_injective g hg
  exact congrArg Subtype.val hwv

def rowEmbed {k L : ℕ} (g : Fin (k + 1) → Fin (L + 1)) : (Fin k → 𝔽₂) →ₗ[𝔽₂] (Fin L → 𝔽₂) :=
  (startBoundaryEquivEven L).symm.toLinearMap.comp ((evenExtend g).comp (startBoundaryEquivEven k).toLinearMap)

theorem rowEmbed_injective {k L : ℕ} (g : Fin (k + 1) → Fin (L + 1)) (hg : Function.Injective g) :
    Function.Injective (rowEmbed g) :=
  (startBoundaryEquivEven L).symm.injective.comp ((evenExtend_injective g hg).comp (startBoundaryEquivEven k).injective)

theorem boundary_rowEmbed {k L : ℕ} (g : Fin (k + 1) → Fin (L + 1)) (u : Fin k → 𝔽₂) :
    startCompleteBoundary L (rowEmbed g u) = extend g (startCompleteBoundary k u) := by
  exact congrArg Subtype.val ((startBoundaryEquivEven L).apply_symm_apply (evenExtend g (startBoundaryEquivEven k u)))

theorem transpose_extend {α β : Type*} [Fintype α] [Fintype β] (g : α → β) (w : β → 𝔽₂) :
    transpose (extend g) w = w ∘ g := by
  funext i
  rw [transpose_apply, extend_single, single_one_dotProduct]
  rfl

theorem selected_relative_identity {k L : ℕ} (g : Fin (k + 1) → Fin (L + 1)) (w : Fin (L + 1) → 𝔽₂) :
    transpose (rowEmbed g) (transpose (startCompleteBoundary L) w) =
      transpose (startCompleteBoundary k) (w ∘ g) := by
  have hmap : (startCompleteBoundary L).comp (rowEmbed g) = (extend g).comp (startCompleteBoundary k) := by
    apply LinearMap.ext
    exact boundary_rowEmbed g
  have h := congrArg (fun c ↦ transpose c w) hmap
  simpa only [transpose_comp, LinearMap.comp_apply, transpose_extend] using h

end PaperP1.SelectedBoundary
