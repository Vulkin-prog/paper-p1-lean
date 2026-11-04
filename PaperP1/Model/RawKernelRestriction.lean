module

public import PaperP1.Model.RawValueLaw
public import PaperP1.Algebra.FinitePiExtensionSupport

/-! # Restricting the actual raw word embeds its unrestricted relation kernel -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RawKernelRestriction

open PaperP1.Arithmetic PaperP1.RawValueLaw

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem combination_extend (e : ι ↪ κ) (v : ι → ℕ) (t : κ → ℕ)
    (hv : ∀ i, t (e i) = v i) (u : ι → F₂) :
    columnMap t (FinitePiExtension.extend e u) = columnMap v u :=
  FinitePiExtension.combination_extend e (fun i ↦ parityVec (v i))
    (fun j ↦ parityVec (t j)) (fun i ↦ congrArg parityVec (hv i)) u

def kernelEmbedding (e : ι ↪ κ) (v : ι → ℕ) (t : κ → ℕ)
    (hv : ∀ i, t (e i) = v i) :
    LinearMap.ker (columnMap v) →ₗ[F₂] LinearMap.ker (columnMap t) where
  toFun u := ⟨FinitePiExtension.extend e u.val, by
    rw [LinearMap.mem_ker, combination_extend e v t hv]
    exact u.property⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

theorem kernelEmbedding_injective (e : ι ↪ κ) (v : ι → ℕ) (t : κ → ℕ)
    (hv : ∀ i, t (e i) = v i) : Function.Injective (kernelEmbedding e v t hv) := by
  intro u w he
  apply Subtype.ext
  exact FinitePiExtensionSupport.extend_injective e (congrArg Subtype.val he)

theorem finrank_le (e : ι ↪ κ) (v : ι → ℕ) (t : κ → ℕ)
    (hv : ∀ i, t (e i) = v i) :
    Module.finrank F₂ (LinearMap.ker (columnMap v)) ≤
      Module.finrank F₂ (LinearMap.ker (columnMap t)) :=
  LinearMap.finrank_le_finrank_of_injective (kernelEmbedding_injective e v t hv)

end PaperP1.RawKernelRestriction
