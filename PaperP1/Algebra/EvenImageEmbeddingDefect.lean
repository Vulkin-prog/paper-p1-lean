module

public import PaperP1.Algebra.FinitePiExtension

/-! # An actual finite even-selection embedding cannot increase the kernel defect -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.EvenImageEmbeddingDefect

variable {K ι κ E : Type*} [DivisionRing K] [Fintype ι] [Fintype κ]
  [AddCommGroup E] [Module K E]

omit [Fintype κ] in
theorem extend_outside (e : ι ↪ κ) (w : ι → K) (x : κ) (hx : ∀ i, e i ≠ x) :
    FinitePiExtension.extend e w x = 0 := by
  classical
  rw [FinitePiExtension.extend_apply, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  simp only [Pi.single_eq_of_ne (hx i).symm]

def kernelEmbedding (e : ι ↪ κ) (f : ι → E) (g : κ → E) (hfg : ∀ i, g (e i) = f i) :
    LinearMap.ker (EvenImage.evenMap (K := K) f) →ₗ[K] LinearMap.ker (EvenImage.evenMap (K := K) g) :=
  ((FinitePiExtension.extendEven e).comp (LinearMap.ker (EvenImage.evenMap (K := K) f)).subtype).codRestrict _ (by
    intro w
    change EvenImage.evenMap g (FinitePiExtension.extendEven e w.val) = 0
    rw [FinitePiExtension.evenMap_extend e f g hfg]
    exact w.property)

theorem kernel_embedding_injective (e : ι ↪ κ) (f : ι → E) (g : κ → E) (hfg : ∀ i, g (e i) = f i) :
    Function.Injective (kernelEmbedding (K := K) e f g hfg) := by
  intro u v h
  apply Subtype.ext
  exact FinitePiExtension.extendEven_injective (K := K) e (congrArg Subtype.val h)

theorem kernel_rank_le (e : ι ↪ κ) (f : ι → E) (g : κ → E) (hfg : ∀ i, g (e i) = f i) :
    Module.finrank K (LinearMap.ker (EvenImage.evenMap (K := K) f)) ≤
      Module.finrank K (LinearMap.ker (EvenImage.evenMap (K := K) g)) :=
  LinearMap.finrank_le_finrank_of_injective (kernel_embedding_injective (K := K) e f g hfg)

theorem image_defect_bound (e : ι ↪ κ) (f : ι → E) (g : κ → E) (hfg : ∀ i, g (e i) = f i) :
    Fintype.card ι - 1 ≤ Module.finrank K (EvenImage.image (K := K) f) +
      ((Fintype.card κ - 1) - Module.finrank K (EvenImage.image (K := K) g)) := by
  have hker := kernel_rank_le (K := K) e f g hfg
  have hf := (EvenImage.evenMap (K := K) f).finrank_range_add_finrank_ker
  have hg := (EvenImage.evenMap (K := K) g).finrank_range_add_finrank_ker
  rw [EvenSupportRank.kernel_sum_finrank] at hf hg
  change Module.finrank K (EvenImage.image (K := K) f) + _ = _ at hf
  change Module.finrank K (EvenImage.image (K := K) g) + _ = _ at hg
  omega

end PaperP1.EvenImageEmbeddingDefect
