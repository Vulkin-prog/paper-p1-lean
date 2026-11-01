module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Pi

/-! # A supported zero-sum space has dimension at most card(support)-1 -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.EvenSupportRank

open Finset

variable {K ι : Type*} [DivisionRing K] [Fintype ι]

def sumMap (K ι : Type*) [DivisionRing K] [Fintype ι] : (ι → K) →ₗ[K] K :=
  Fintype.linearCombination K (fun _ ↦ 1)

theorem sumMap_apply (w : ι → K) : sumMap K ι w = ∑ i, w i := by
  simp only [sumMap, Fintype.linearCombination_apply, smul_eq_mul, mul_one]

theorem kernel_sum_finrank : Module.finrank K (LinearMap.ker (sumMap K ι)) = Fintype.card ι - 1 := by
  classical
  by_cases hι : Nonempty ι
  · let i := Classical.choice hι
    have hsurj : Function.Surjective (sumMap K ι) := by
      intro c
      refine ⟨Pi.single i c, ?_⟩
      simp [sumMap_apply]
    have hdim := (sumMap K ι).finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hsurj] at hdim
    simp at hdim
    omega
  · have : IsEmpty ι := not_nonempty_iff.mp hι
    have hbound := (LinearMap.ker (sumMap K ι)).finrank_le
    simpa using hbound

variable {E : Type*} [AddCommGroup E] [Module K E]

theorem finrank_le_of_supported_even (g : E →ₗ[K] (ι → K)) (hg : Function.Injective g)
    (T : Finset ι) (hzero : ∀ e i, i ∉ T → g e i = 0)
    (heven : ∀ e, ∑ i, g e i = 0) : Module.finrank K E ≤ T.card - 1 := by
  classical
  let r : E →ₗ[K] (T → K) :=
    { toFun := fun e i ↦ g e i.val
      map_add' := by intros; funext; simp only [map_add, Pi.add_apply]
      map_smul' := by intros; funext; simp only [map_smul, Pi.smul_apply, RingHom.id_apply] }
  have hr (e : E) : r e ∈ LinearMap.ker (sumMap K T) := by
    rw [LinearMap.mem_ker, sumMap_apply]
    change (∑ i : T, g e i.val) = 0
    rw [sum_coe_sort T (fun i ↦ g e i)]
    exact (sum_subset (subset_univ T) (fun i _ hi ↦ hzero e i hi)).trans (heven e)
  let f := r.codRestrict (LinearMap.ker (sumMap K T)) hr
  have hinj : Function.Injective f := by
    intro e e' hee
    apply hg
    funext i
    by_cases hi : i ∈ T
    · exact congrFun (congrArg Subtype.val hee) ⟨i, hi⟩
    · rw [hzero e i hi, hzero e' i hi]
  have hdim := LinearMap.finrank_le_finrank_of_injective hinj
  simpa only [kernel_sum_finrank, Fintype.card_coe] using hdim

end PaperP1.EvenSupportRank
