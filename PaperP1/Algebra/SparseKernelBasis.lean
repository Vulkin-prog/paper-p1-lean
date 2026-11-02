module

public import PaperP1.Algebra.SupportedLinearSection

/-! # Every finite-rank system has a kernel basis supported on at most rank plus one columns -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SparseKernelBasis

open Finset PaperP1.SupportedLinearSection

universe u v w
variable {K : Type u} {V : Type v} {J : Type w} [DivisionRing K] [AddCommGroup V] [Module K V]

local instance : AddCommGroup (J →₀ K) := inferInstance
local instance (S : Submodule K (J →₀ K)) : AddCommGroup S := inferInstance

theorem kernel_basis_from_section (f : (J →₀ K) →ₗ[K] V) (S : Finset J)
    (s : LinearMap.range f →ₗ[K] (J →₀ K)) (hs : ∀ x, f (s x) = x.val)
    (hsupport : ∀ x, (s x).support ⊆ S) :
    ∃ (I : Type (max u w)) (b : Module.Basis I K (LinearMap.ker f)),
      ∀ i, (b i).val.support.card ≤ S.card + 1 := by
  classical
  let g : (J →₀ K) →ₗ[K] (J →₀ K) := LinearMap.id - s.comp f.rangeRestrict
  have hg (x : J →₀ K) : g x ∈ LinearMap.ker f := by
    rw [LinearMap.mem_ker]
    change f (x - s (f.rangeRestrict x)) = 0
    rw [map_sub, hs]
    exact sub_self _
  let q : (J →₀ K) →ₗ[K] LinearMap.ker f := g.codRestrict (LinearMap.ker f) hg
  have hsurj : Function.Surjective q := by
    intro x
    refine ⟨x.val, ?_⟩
    apply Subtype.ext
    change x.val - s (f.rangeRestrict x.val) = x.val
    have hf : f.rangeRestrict x.val = 0 := Subtype.ext (LinearMap.mem_ker.mp x.property)
    rw [hf, map_zero, sub_zero]
  let columns : J → LinearMap.ker f := fun j ↦ q (Finsupp.single j 1)
  have hspan : Submodule.span K (Set.range columns) = ⊤ :=
    (span_single_images (K := K) (V := LinearMap.ker f) (J := J) q).trans
      (LinearMap.range_eq_top.mpr hsurj)
  let I : Set (LinearMap.ker f) :=
    (linearIndepOn_empty K (id : LinearMap.ker f → LinearMap.ker f)).extend
      (Set.empty_subset (Set.range columns))
  let b : Module.Basis I K (LinearMap.ker f) := Module.Basis.ofSpan (K := K) (V := LinearMap.ker f) hspan.ge
  refine ⟨I, b, ?_⟩
  intro i
  obtain ⟨j, hj⟩ := Module.Basis.ofSpan_subset (K := K) (V := LinearMap.ker f) hspan.ge (Set.mem_range_self i)
  change q (Finsupp.single j 1) = b i at hj
  rw [← hj]
  have hsub : (q (Finsupp.single j 1)).val.support ⊆ insert j S := by
    intro k hk
    by_contra hn
    have hnot : k ∉ S := fun h ↦ hn (mem_insert_of_mem h)
    have hne : j ≠ k := by
      intro he
      subst k
      exact hn (mem_insert_self _ _)
    have hs0 : s (f.rangeRestrict (Finsupp.single j 1)) k = 0 :=
      Finsupp.notMem_support_iff.mp (fun h ↦ hnot (hsupport _ h))
    have hz : (q (Finsupp.single j 1)).val k = 0 := by
      change ((Finsupp.single j (1 : K) - s (f.rangeRestrict (Finsupp.single j 1)) : J →₀ K)) k = 0
      rw [Finsupp.sub_apply, Finsupp.single_apply, ite_eq_right hne, hs0, sub_self]
    exact (Finsupp.mem_support_iff.mp hk) hz
  exact (card_le_card hsub).trans (card_insert_le j S)

theorem exists_sparse_kernel_basis [Module.Finite K V] (f : (J →₀ K) →ₗ[K] V) :
    ∃ (I : Type (max u w)) (b : Module.Basis I K (LinearMap.ker f)),
      ∀ i, (b i).val.support.card ≤ Module.finrank K V + 1 := by
  obtain ⟨S, s, hS, hs, hsupport⟩ := exists_supported_section f
  obtain ⟨I, b, hb⟩ := kernel_basis_from_section f S s hs hsupport
  exact ⟨I, b, fun i ↦ (hb i).trans (Nat.add_le_add_right hS 1)⟩

theorem finite_equations {P : Type*} [Fintype P] (f : (J →₀ K) →ₗ[K] (P → K)) :
    ∃ (I : Type (max u w)) (b : Module.Basis I K (LinearMap.ker f)),
      ∀ i, (b i).val.support.card ≤ Fintype.card P + 1 := by
  simpa only [Module.finrank_fintype_fun_eq_card] using exists_sparse_kernel_basis f

end PaperP1.SparseKernelBasis
