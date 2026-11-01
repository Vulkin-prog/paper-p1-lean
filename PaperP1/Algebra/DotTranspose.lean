module

public import PaperP1.Affine.IndependentRows

/-! # The transpose of an injective binary coordinate map has a fair output law -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DotTranspose

open Finset PaperP1.Affine

local instance dotTransposeDecidable (P : Prop) : Decidable P := Classical.propDecidable P

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

def transpose (c : (α → 𝔽₂) →ₗ[𝔽₂] (β → 𝔽₂)) : (β → 𝔽₂) →ₗ[𝔽₂] (α → 𝔽₂) := by
  classical
  exact LinearMap.pi fun i ↦ dotLinear (c (Pi.single i 1))

omit [Fintype α] in
theorem transpose_apply (c : (α → 𝔽₂) →ₗ[𝔽₂] (β → 𝔽₂)) (v : β → 𝔽₂) (i : α) :
    transpose c v i = dotProduct (c (Pi.single i 1)) v := rfl

omit [Fintype β] in
theorem basis_expansion (c : (α → 𝔽₂) →ₗ[𝔽₂] (β → 𝔽₂)) (u : α → 𝔽₂) :
    c u = ∑ i, u i • c (Pi.single i 1) := by
  classical
  have hb : (∑ i, Pi.single i (u i)) = u := by
    funext j
    simpa only [Finset.sum_apply] using Fintype.sum_pi_single j u
  calc
    _ = c (∑ i, Pi.single i (u i)) := congrArg c hb.symm
    _ = ∑ i, c (Pi.single i (u i)) := map_sum c _ _
    _ = _ := by
      apply sum_congr rfl
      intro i _
      have hi : Pi.single i (u i) = u i • (Pi.single i (1 : 𝔽₂)) := by
        funext j
        by_cases hj : j = i <;> simp [hj]
      rw [hi, map_smul]

theorem pairing (c : (α → 𝔽₂) →ₗ[𝔽₂] (β → 𝔽₂)) (u : α → 𝔽₂) (v : β → 𝔽₂) :
    dotProduct u (transpose c v) = dotProduct (c u) v := by
  change (∑ i, u i * dotProduct (c (Pi.single i 1)) v) = _
  rw [basis_expansion c u, sum_dotProduct]
  simp only [smul_dotProduct, smul_eq_mul]

omit [Fintype α] in
theorem transpose_comp (c : (α → 𝔽₂) →ₗ[𝔽₂] (β → 𝔽₂))
    (d : (β → 𝔽₂) →ₗ[𝔽₂] (γ → 𝔽₂)) :
    transpose (d.comp c) = (transpose c).comp (transpose d) := by
  apply LinearMap.ext
  intro w
  funext i
  change dotProduct (d (c (Pi.single i 1))) w = dotProduct (c (Pi.single i 1)) (transpose d w)
  exact (pairing d (c (Pi.single i 1)) w).symm

theorem relationMap_injective (c : (α → 𝔽₂) →ₗ[𝔽₂] (β → 𝔽₂)) (hc : Function.Injective c) :
    Function.Injective (relationMap (transpose c)) := by
  intro u v huv
  apply hc
  apply dotProduct_eq
  intro w
  have h := DFunLike.congr_fun huv w
  change dotProduct u (transpose c w) = dotProduct v (transpose c w) at h
  simpa only [pairing] using h

end PaperP1.DotTranspose
