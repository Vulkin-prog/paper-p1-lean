module

public import PaperP1.Algebra.SupportedLinearSection
public import PaperP1.Algebra.LinearCombinationSupport
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Basis.Basic
public import Lean.Elab.Tactic.Omega

/-! # Deleting one actual witness coordinate builds independent short kernel vectors -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GreedyShortKernel

open Finset

universe u v w
variable {K : Type u} {V : Type v} {E : Type w} [DivisionRing K] [AddCommGroup V] [Module K V]

local instance : AddCommGroup (E →₀ K) := inferInstance
local instance (U : Submodule K (E →₀ K)) : AddCommGroup U := inferInstance

def HasShortVector (f : (E →₀ K) →ₗ[K] V) (S : Finset E) (k : ℕ) : Prop :=
  ∃ x : LinearMap.ker f, x ≠ 0 ∧ x.val.support ⊆ S ∧ x.val.support.card ≤ k

theorem mono (f : (E →₀ K) →ₗ[K] V) {S T : Finset E} {k ℓ : ℕ}
    (h : HasShortVector f S k) (hST : S ⊆ T) (hk : k ≤ ℓ) : HasShortVector f T ℓ := by
  obtain ⟨x, hx, hs, hsize⟩ := h
  exact ⟨x, hx, hs.trans hST, hsize.trans hk⟩

theorem independent_family (f : (E →₀ K) →ₗ[K] V) (Q : Finset E) (r k : ℕ)
    (hfind : ∀ S ⊆ Q, r < S.card → HasShortVector f S k) :
    ∃ (n : ℕ) (v : Fin n → LinearMap.ker f), LinearIndependent K v ∧ Q.card - r ≤ n ∧
      (∀ i, (v i).val.support ⊆ Q) ∧ (∀ i, (v i).val.support.card ≤ k) := by
  classical
  revert hfind
  induction Q using Finset.strongInductionOn with
  | _ Q ih =>
    intro hfind
    by_cases hsmall : Q.card ≤ r
    · refine ⟨0, (fun i : Fin 0 ↦ Fin.elim0 i), linearIndependent_empty_type, ?_,
        (fun i ↦ Fin.elim0 i), (fun i ↦ Fin.elim0 i)⟩
      omega
    obtain ⟨x, hx, hsupport, hsize⟩ := hfind Q (subset_refl Q) (by omega)
    have hxval : x.val ≠ 0 := fun h ↦ hx (Subtype.ext h)
    obtain ⟨j, hj⟩ := Finsupp.support_nonempty_iff.mpr hxval
    have hjQ := hsupport hj
    obtain ⟨n, v, hli, hn, hs, hk⟩ := ih (Q.erase j) (erase_ssubset hjQ)
      (fun S hS hlarge ↦ hfind S (hS.trans (erase_subset _ _)) hlarge)
    let coord : LinearMap.ker f →ₗ[K] K := (Finsupp.lapply j).comp (LinearMap.ker f).subtype
    have hzero : Submodule.span K (Set.range v) ≤ LinearMap.ker coord := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      change (v i).val j = 0
      apply Finsupp.notMem_support_iff.mp
      intro hjv
      exact (mem_erase.mp (hs i hjv)).1 rfl
    have hnot : x ∉ Submodule.span K (Set.range v) := by
      intro h
      have hz : x.val j = 0 := LinearMap.mem_ker.mp (hzero h)
      exact (Finsupp.mem_support_iff.mp hj) hz
    have hcard := card_erase_add_one hjQ
    refine ⟨n + 1, Fin.cons x v, hli.finCons hnot, by omega, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun t ↦ ?_) i
      · simpa only [Fin.cons_zero] using hsupport
      · simpa only [Fin.cons_succ] using (hs t).trans (erase_subset j Q)
    · intro i
      refine Fin.cases ?_ (fun t ↦ ?_) i
      · simpa only [Fin.cons_zero] using hsize
      · simpa only [Fin.cons_succ] using hk t

theorem sparse_subspace_basis (f : (E →₀ K) →ₗ[K] V) (Q : Finset E) (r k : ℕ)
    (hfind : ∀ S ⊆ Q, r < S.card → HasShortVector f S k) :
    ∃ (n : ℕ) (U : Submodule K (LinearMap.ker f)) (b : Module.Basis (Fin n) K U),
      Q.card - r ≤ Module.finrank K U ∧
      (∀ i, (b i).val.val.support ⊆ Q) ∧ (∀ i, (b i).val.val.support.card ≤ k) := by
  obtain ⟨n, v, hli, hn, hs, hk⟩ := independent_family f Q r k hfind
  let U := Submodule.span K (Set.range v)
  let b : Module.Basis (Fin n) K U := Module.Basis.span hli
  have hb (i : Fin n) : (b i).val = v i := Module.Basis.coe_span_apply hli i
  have hdim : Module.finrank K U = n := by
    simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis b
  refine ⟨n, U, b, by omega, ?_, ?_⟩
  · intro i
    rw [hb]
    exact hs i
  · intro i
    rw [hb]
    exact hk i

theorem physical_subspace_basis {A : Type*} (f : (E →₀ K) →ₗ[K] V) (g : (E →₀ K) →ₗ[K] (A →₀ K))
    (Q : Finset E) (r k M : ℕ) (hfind : ∀ S ⊆ Q, r < S.card → HasShortVector f S k)
    (hphysical : ∀ e, (g (Finsupp.single e 1)).support.card ≤ M) :
    ∃ (n : ℕ) (U : Submodule K (LinearMap.ker f)) (b : Module.Basis (Fin n) K U),
      Q.card - r ≤ Module.finrank K U ∧ ∀ i, (g (b i).val.val).support.card ≤ M * k := by
  classical
  obtain ⟨n, U, b, hdim, _hs, hk⟩ := sparse_subspace_basis f Q r k hfind
  refine ⟨n, U, b, hdim, ?_⟩
  intro i
  rw [SupportedLinearSection.map_eq_linearCombination g]
  exact (LinearCombinationSupport.card_le (fun e ↦ g (Finsupp.single e 1)) (b i).val.val M hphysical).trans
    (Nat.mul_le_mul_left M (hk i))

end PaperP1.GreedyShortKernel
