module

public import PaperP1.Arithmetic.FiniteEvenSquareClasses

/-! # An even combination supported on actual values belongs to their exact even square-class space -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SupportedEvenSquareClasses

open Finset PaperP1.Arithmetic PaperP1.FiniteEvenSquareClasses

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem combination_mem {ι : Type*} [Fintype ι] (value : ι → ℕ) (w : ι → F₂)
    (S : Finset ℕ) (heven : (∑ i, w i) = 0)
    (hzero : ∀ i, value i ∉ S → w i = 0) :
    (∑ i, w i • parityVec (value i)) ∈ space S := by
  classical
  by_cases hS : S.Nonempty
  · obtain ⟨a, ha⟩ := hS
    have hterm (i : ι) : w i • (parityVec (value i) - parityVec a) ∈ space S := by
      by_cases hi : value i ∈ S
      · apply Submodule.smul_mem
        rw [space_eq_span S a ha]
        exact Submodule.subset_span ⟨value i, hi, rfl⟩
      · rw [hzero i hi, zero_smul]
        exact Submodule.zero_mem _
    have hsum := Submodule.sum_mem (space S) (fun i (_hi : i ∈ (univ : Finset ι)) ↦ hterm i)
    have heq : (∑ i, w i • (parityVec (value i) - parityVec a)) =
        ∑ i, w i • parityVec (value i) := by
      simp_rw [smul_sub]
      rw [sum_sub_distrib, ← sum_smul, heven, zero_smul, sub_zero]
    rwa [heq] at hsum
  · have hz : ∀ i, w i = 0 := fun i ↦ hzero i (fun hi ↦ hS ⟨value i, hi⟩)
    simp only [hz, zero_smul, sum_const_zero]
    exact Submodule.zero_mem _

end PaperP1.SupportedEvenSquareClasses
