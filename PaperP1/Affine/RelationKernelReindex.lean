module

public import PaperP1.Affine.Relations
public import Mathlib.Algebra.Module.Submodule.Equiv

/-! # Exact index transport of actual addition kernels and their projections -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RelationKernelReindex

open Finset PaperP1.Affine

variable {U ι κ : Type*} [AddCommGroup U] [Module 𝔽₂ U] [Fintype ι] [Fintype κ]

local instance : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

theorem addition_pullback (S : ι → Submodule 𝔽₂ U) (e : κ ≃ ι) (r : (i : ι) → S i) :
    relationAddition (fun j ↦ S (e j)) (fun j ↦ r (e j)) = relationAddition S r := by
  exact Fintype.sum_equiv e _ _ (fun _ ↦ rfl)

def kernelEquiv (S : ι → Submodule 𝔽₂ U) (e : κ ≃ ι) :
    LinearMap.ker (relationAddition S) ≃ₗ[𝔽₂] LinearMap.ker (relationAddition (fun j ↦ S (e j))) := by
  let E := LinearEquiv.piCongrLeft 𝔽₂ (fun i ↦ S i) e
  apply E.symm.ofSubmodules
  ext r
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact (addition_pullback S e v).trans hv
  · intro hr
    refine ⟨E r, ?_, E.symm_apply_apply r⟩
    have hh := addition_pullback S e (E r)
    change relationAddition (fun j ↦ S (e j)) (E.symm (E r)) = relationAddition S (E r) at hh
    rw [E.symm_apply_apply] at hh
    exact hh.symm.trans hr

theorem kernelEquiv_apply (S : ι → Submodule 𝔽₂ U) (e : κ ≃ ι)
    (r : LinearMap.ker (relationAddition S)) (j : κ) :
    (kernelEquiv S e r).val j = r.val (e j) := rfl

theorem finrank_eq (S : ι → Submodule 𝔽₂ U) (e : κ ≃ ι) :
    Module.finrank 𝔽₂ (LinearMap.ker (relationAddition (fun j ↦ S (e j)))) =
      Module.finrank 𝔽₂ (LinearMap.ker (relationAddition S)) :=
  (kernelEquiv S e).finrank_eq.symm

theorem projection_injective (S : ι → Submodule 𝔽₂ U) (e : κ ≃ ι) (j : κ)
    (hinj : Function.Injective ((LinearMap.proj (e j)).comp (LinearMap.ker (relationAddition S)).subtype)) :
    Function.Injective ((LinearMap.proj j).comp (LinearMap.ker (relationAddition (fun k ↦ S (e k)))).subtype) := by
  intro r t he
  let E := kernelEquiv S e
  apply E.symm.injective
  apply hinj
  have hr := congrArg (fun q : LinearMap.ker (relationAddition (fun k ↦ S (e k))) ↦ q.val j)
    (E.apply_symm_apply r)
  have ht := congrArg (fun q : LinearMap.ker (relationAddition (fun k ↦ S (e k))) ↦ q.val j)
    (E.apply_symm_apply t)
  exact hr.trans (he.trans ht.symm)

end PaperP1.RelationKernelReindex
