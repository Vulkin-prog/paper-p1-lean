module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # A section of a finite-rank linear map supported on actual pivot columns -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SupportedLinearSection

open Finset

universe u v w
variable {K : Type u} {V : Type v} {J : Type w} [DivisionRing K] [AddCommGroup V] [Module K V]

theorem map_eq_linearCombination (f : (J →₀ K) →ₗ[K] V) :
    f = Finsupp.linearCombination K (fun j ↦ f (Finsupp.single j 1)) := by
  apply Finsupp.lhom_ext
  intro j a
  rw [Finsupp.linearCombination_single]
  have hs : Finsupp.single j a = a • Finsupp.single j (1 : K) := by simp
  rw [hs, map_smul]

theorem span_single_images (f : (J →₀ K) →ₗ[K] V) :
    Submodule.span K (Set.range (fun j ↦ f (Finsupp.single j 1))) = LinearMap.range f := by
  rw [← Finsupp.range_linearCombination, ← map_eq_linearCombination f]

theorem exists_supported_section [Module.Finite K V] (f : (J →₀ K) →ₗ[K] V) :
    ∃ (S : Finset J) (s : LinearMap.range f →ₗ[K] (J →₀ K)), S.card ≤ Module.finrank K V ∧
      (∀ x, f (s x) = x.val) ∧ (∀ x, (s x).support ⊆ S) := by
  classical
  let columns : J → LinearMap.range f := fun j ↦ f.rangeRestrict (Finsupp.single j 1)
  have hspan : Submodule.span K (Set.range columns) = ⊤ := by
    exact (span_single_images f.rangeRestrict).trans (LinearMap.range_rangeRestrict f)
  let I : Set (LinearMap.range f) :=
    (linearIndepOn_empty K (id : LinearMap.range f → LinearMap.range f)).extend
      (Set.empty_subset (Set.range columns))
  let b : Module.Basis I K (LinearMap.range f) := Module.Basis.ofSpan hspan.ge
  let : Finite I := Module.Finite.finite_basis b
  let : Fintype I := Fintype.ofFinite I
  have hchoose (i : I) : ∃ j : J, columns j = b i :=
    Module.Basis.ofSpan_subset hspan.ge (Set.mem_range_self i)
  choose pivot hpivot using hchoose
  let S : Finset J := univ.image pivot
  let s : LinearMap.range f →ₗ[K] (J →₀ K) :=
    (Finsupp.linearCombination K (fun i : I ↦ Finsupp.single (pivot i) 1)).comp b.repr.toLinearMap
  refine ⟨S, s, ?_, ?_, ?_⟩
  · calc
      S.card ≤ Fintype.card I := card_image_le.trans_eq (Finset.card_univ : (univ : Finset I).card = _)
      _ = Module.finrank K (LinearMap.range f) := (Module.finrank_eq_card_basis b).symm
      _ ≤ Module.finrank K V := (LinearMap.range f).finrank_le
  · intro x
    have hp (i : I) : f (Finsupp.single (pivot i) 1) = (b i).val := congrArg Subtype.val (hpivot i)
    change f (Finsupp.linearCombination K (fun i : I ↦ Finsupp.single (pivot i) 1) (b.repr x)) = x.val
    rw [Finsupp.apply_linearCombination]
    have he : (f ∘ fun i : I ↦ Finsupp.single (pivot i) 1) = (fun i : I ↦ (b i).val) := by
      funext i
      exact hp i
    rw [he]
    have he' : ((LinearMap.range f).subtype ∘ b) = (fun i : I ↦ (b i).val) := rfl
    have hm := Finsupp.apply_linearCombination K (LinearMap.range f).subtype b (b.repr x)
    rw [he'] at hm
    exact hm.symm.trans (congrArg Subtype.val (b.linearCombination_repr x))
  · intro x j hj
    by_contra hn
    have hz : s x j = 0 := by
      change (Finsupp.linearCombination K (fun i : I ↦ Finsupp.single (pivot i) 1) (b.repr x)) j = 0
      rw [Finsupp.linearCombination_apply]
      simp only [Finsupp.sum, Finset.sum_apply', Finsupp.smul_apply]
      apply sum_eq_zero
      intro i _hi
      have hne : pivot i ≠ j := by
        intro he
        exact hn (mem_image.mpr ⟨i, mem_univ _, he⟩)
      rw [Finsupp.single_apply, ite_eq_right hne, smul_zero]
    exact (Finsupp.mem_support_iff.mp hj) hz

end PaperP1.SupportedLinearSection
