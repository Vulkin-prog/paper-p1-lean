module

public import PaperP1.Algebra.EvenSupportRank
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Images of zero-sum selections and their anchored difference generators -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.EvenImage

open Finset

variable {K ι E : Type*} [DivisionRing K] [Fintype ι] [AddCommGroup E] [Module K E]

def combination (data : ι → E) : (ι → K) →ₗ[K] E := Fintype.linearCombination K data

def evenMap (data : ι → E) : LinearMap.ker (EvenSupportRank.sumMap K ι) →ₗ[K] E :=
  (combination data).comp (LinearMap.ker (EvenSupportRank.sumMap K ι)).subtype

def image (data : ι → E) : Submodule K E := LinearMap.range (evenMap data)

theorem combination_apply (data : ι → E) (w : ι → K) :
    combination data w = ∑ i, w i • data i := by
  simp only [combination, Fintype.linearCombination_apply]

theorem mem_image_iff (data : ι → E) (z : E) :
    z ∈ image (K := K) data ↔ ∃ w : ι → K, (∑ i, w i) = 0 ∧ combination data w = z := by
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨w, by simpa only [LinearMap.mem_ker, EvenSupportRank.sumMap_apply] using w.2, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨⟨w, by simpa only [LinearMap.mem_ker, EvenSupportRank.sumMap_apply] using hw⟩, rfl⟩

theorem difference_mem (data : ι → E) (i j : ι) : data i - data j ∈ image (K := K) data := by
  classical
  apply (mem_image_iff data _).mpr
  refine ⟨Pi.single i 1 - Pi.single j 1, ?_, ?_⟩
  · simp only [Pi.sub_apply, sum_sub_distrib, Fintype.sum_pi_single', sub_self]
  · rw [map_sub]
    simp only [combination, Fintype.linearCombination_apply_single, one_smul]

theorem image_eq_span_differences (data : ι → E) (j : ι) :
    image (K := K) data = Submodule.span K (Set.range fun i ↦ data i - data j) := by
  apply le_antisymm
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := (mem_image_iff data z).mp hz
    have heq : combination data w = ∑ i, w i • (data i - data j) := by
      rw [combination_apply]
      simp only [smul_sub, sum_sub_distrib, ← sum_smul, hw, zero_smul, sub_zero]
    rw [heq]
    exact Submodule.sum_mem _ (fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact difference_mem data i j

theorem evenMap_injective (data : ι → E) (hinj : Function.Injective (combination (K := K) data)) :
    Function.Injective (evenMap (K := K) data) := by
  intro w z hwz
  apply Subtype.ext
  exact hinj hwz

theorem finrank_of_injective (data : ι → E) (hinj : Function.Injective (combination (K := K) data)) :
    Module.finrank K (image (K := K) data) = Fintype.card ι - 1 := by
  have heven := evenMap_injective data hinj
  rw [image, LinearMap.finrank_range_of_inj heven, EvenSupportRank.kernel_sum_finrank]

end PaperP1.EvenImage
