module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Lean.Elab.Tactic.Omega

/-! # Simultaneously making finitely many projections injective at their exact kernel cost

A complement to the sum of the kernels suffices; the kernels need not be direct.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CommonInjectiveRestriction

open Finset

variable {K U ι : Type*} [DivisionRing K] [AddCommGroup U] [Module K U]
  [FiniteDimensional K U] [DecidableEq ι]

theorem finrank_finite_sup (S : ι → Submodule K U) (A : Finset ι) :
    Module.finrank K ↥(A.sup S) ≤ ∑ i ∈ A, Module.finrank K (S i) := by
  induction A using Finset.induction_on with
  | empty => rw [Finset.sup_empty, finrank_bot, sum_empty]
  | @insert i A hi ih =>
    rw [Finset.sup_insert, sum_insert hi]
    exact (Submodule.finrank_add_le_finrank_add_finrank (S i) (A.sup S)).trans
      (Nat.add_le_add_left ih _)

theorem exists_subspace [Fintype ι] {V : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] (f : (i : ι) → U →ₗ[K] V i) :
    ∃ M : Submodule K U,
      Module.finrank K U ≤ Module.finrank K M + ∑ i, Module.finrank K (LinearMap.ker (f i)) ∧
      ∀ i, Function.Injective ((f i).comp M.subtype) := by
  classical
  let R : Submodule K U := (univ : Finset ι).sup fun i ↦ LinearMap.ker (f i)
  obtain ⟨M, hM⟩ := Submodule.exists_isCompl R
  have hdim := Submodule.finrank_add_eq_of_isCompl hM
  have hbound := finrank_finite_sup (fun i ↦ LinearMap.ker (f i)) univ
  change Module.finrank K R ≤ ∑ i, Module.finrank K (LinearMap.ker (f i)) at hbound
  refine ⟨M, by omega, ?_⟩
  intro i
  apply (injective_iff_map_eq_zero ((f i).comp M.subtype)).mpr
  intro u hu
  apply Subtype.ext
  have hker : u.val ∈ LinearMap.ker (f i) := hu
  have hR : u.val ∈ R := (le_sup (f := fun i ↦ LinearMap.ker (f i)) (mem_univ i)) hker
  exact (Submodule.disjoint_def.mp hM.disjoint) _ hR u.property

end PaperP1.CommonInjectiveRestriction
