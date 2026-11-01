module

public import PaperP1.Algebra.EvenImage

/-! # Zero-sum images commute with every linear observation map -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.EvenImageMap

variable {K ι E F : Type*} [DivisionRing K] [Fintype ι]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]

theorem evenMap_map (g : E →ₗ[K] F) (f : ι → E) :
    EvenImage.evenMap (K := K) (fun i ↦ g (f i)) = g.comp (EvenImage.evenMap (K := K) f) := by
  ext w
  change EvenImage.combination (K := K) (fun i ↦ g (f i)) w.val = g (EvenImage.combination (K := K) f w.val)
  simp only [EvenImage.combination_apply, map_sum, map_smul]

theorem image_map (g : E →ₗ[K] F) (f : ι → E) :
    EvenImage.image (K := K) (fun i ↦ g (f i)) = (EvenImage.image (K := K) f).map g := by
  rw [EvenImage.image, evenMap_map, LinearMap.range_comp]
  rfl

end PaperP1.EvenImageMap
