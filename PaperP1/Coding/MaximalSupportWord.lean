module

public import PaperP1.Algebra.BinaryEvenSelections
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # A maximal-support codeword has weight at least the code dimension -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MaximalSupportWord

open Finset PaperP1.Arithmetic PaperP1.BinaryEvenSelections

local instance maximalSupportPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {ι : Type*} [Fintype ι]

theorem exists_large_word (C : Submodule F₂ (ι → F₂)) :
    ∃ w : C, Module.finrank F₂ C ≤ (selected w.val).card := by
  classical
  obtain ⟨w, hw⟩ := Finite.exists_max (fun w : C ↦ (selected w.val).card)
  let S := selected w.val
  let p : C →ₗ[F₂] (S → F₂) :=
    (LinearMap.pi fun i : S ↦ LinearMap.proj i.val).comp C.subtype
  have hinj : Function.Injective p := by
    apply (injective_iff_map_eq_zero p).mpr
    intro x hx
    by_contra hx0
    have hzero (i : ι) (hi : i ∈ S) : x.val i = 0 := congrFun hx ⟨i, hi⟩
    have hxne : x.val ≠ 0 := fun h ↦ hx0 (Subtype.ext h)
    obtain ⟨j, hj⟩ := (selected_nonempty_iff x.val).mpr hxne
    have hjx : x.val j ≠ 0 := (mem_filter.mp hj).2
    have hjS : j ∉ S := fun hjS ↦ hjx (hzero j hjS)
    have hwj : w.val j = 0 := by
      by_contra hwj
      exact hjS (mem_filter.mpr ⟨mem_univ _, hwj⟩)
    have hsub : S ⊂ selected (w + x).val := by
      apply ssubset_iff_subset_ne.mpr
      refine ⟨?_, ?_⟩
      · intro i hi
        apply mem_filter.mpr
        refine ⟨mem_univ _, ?_⟩
        change w.val i + x.val i ≠ 0
        rw [hzero i hi, add_zero]
        exact (mem_filter.mp hi).2
      · intro heq
        have hjnew : j ∈ selected (w + x).val := by
          apply mem_filter.mpr
          refine ⟨mem_univ _, ?_⟩
          change w.val j + x.val j ≠ 0
          rw [hwj, zero_add]
          exact hjx
        exact hjS (heq.symm ▸ hjnew)
    have hlt := card_lt_card hsub
    have hmax := hw (w + x)
    change (selected w.val).card < (selected (w + x).val).card at hlt
    omega
  refine ⟨w, ?_⟩
  have hdim := LinearMap.finrank_le_finrank_of_injective hinj
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] using hdim

theorem exists_even_large_word (C : Submodule F₂ (ι → F₂))
    (heven : ∀ w : C, (∑ i, w.val i) = 0) (t : ℕ) (ht : Even t)
    (hdim : t - 1 ≤ Module.finrank F₂ C) : ∃ w : C, t ≤ (selected w.val).card := by
  obtain ⟨w, hw⟩ := exists_large_word C
  have hwEven : Even (selected w.val).card := (even_selected_iff w.val).mpr (by
    simpa only [LinearMap.mem_ker, PaperP1.EvenSupportRank.sumMap_apply] using heven w)
  refine ⟨w, ?_⟩
  obtain ⟨k, hk⟩ := ht
  obtain ⟨j, hj⟩ := hwEven
  omega

end PaperP1.MaximalSupportWord
