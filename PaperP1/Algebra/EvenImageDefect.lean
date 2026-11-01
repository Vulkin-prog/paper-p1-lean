module

public import PaperP1.Algebra.EvenImage

/-! # The loss of the even image is bounded by the full value kernel -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.EvenImageDefect

open PaperP1.EvenImage

variable {K ι E : Type*} [DivisionRing K] [Fintype ι] [AddCommGroup E] [Module K E]

def kernelEmbedding (data : ι → E) :
    LinearMap.ker (evenMap (K := K) data) →ₗ[K] LinearMap.ker (combination (K := K) data) where
  toFun w := ⟨w.val.val, w.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem kernelEmbedding_injective (data : ι → E) : Function.Injective (kernelEmbedding (K := K) data) := by
  intro w z hwz
  have h := congrArg (fun v : LinearMap.ker (combination (K := K) data) ↦ v.val) hwz
  change w.val.val = z.val.val at h
  exact Subtype.ext (Subtype.ext h)

theorem dimension_le_image_add_kernel (data : ι → E) :
    Fintype.card ι - 1 ≤ Module.finrank K (image (K := K) data) +
      Module.finrank K (LinearMap.ker (combination (K := K) data)) := by
  have hker := LinearMap.finrank_le_finrank_of_injective (kernelEmbedding_injective (K := K) data)
  have hrank := (evenMap (K := K) data).finrank_range_add_finrank_ker
  rw [EvenSupportRank.kernel_sum_finrank] at hrank
  change Module.finrank K (image (K := K) data) + Module.finrank K (LinearMap.ker (evenMap (K := K) data)) = _ at hrank
  omega

end PaperP1.EvenImageDefect
