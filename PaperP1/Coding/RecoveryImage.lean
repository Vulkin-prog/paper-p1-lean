module

public import PaperP1.Coding.DisjointRecoverySubspace
public import Mathlib.Algebra.Module.Submodule.Map

/-! # Intrinsic recovery exclusion and target projections survive an injective physical lift -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RecoveryImage

open Finset PaperP1.DisjointRecoverySubspace

variable {K U U' V T : Type*} [Field K] [AddCommGroup U] [Module K U]
  [AddCommGroup U'] [Module K U'] [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem pullback_ne_zero (e : U ≃ₗ[K] U') (α : Module.Dual K U') (hα : α ≠ 0) :
    α.comp e.toLinearMap ≠ 0 := by
  intro hz
  apply hα
  ext u
  obtain ⟨v, rfl⟩ := e.surjective u
  exact LinearMap.congr_fun hz v

omit [Fintype V] [DecidableEq V] in
theorem no_recovery_image (f : U →ₗ[K] U') (hf : Function.Injective f)
    (L' : V → Module.Dual K U') (M : Submodule K U) (d t : ℕ)
    (hno : NoDisjointRecovery (fun v ↦ (L' v).comp f) M d t) :
    NoDisjointRecovery L' (M.map f) d t := by
  let e := Submodule.equivMapOfInjective f hf M
  intro α hα A hdisj hcard hrec
  apply hno (α.comp e.toLinearMap) (pullback_ne_zero e α hα) A hdisj hcard
  intro j
  ext m
  have h := LinearMap.congr_fun (hrec j) (e m)
  simpa only [e, LinearMap.sum_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    Submodule.subtype_apply, Submodule.coe_equivMapOfInjective_apply] using h

omit [Fintype V] [DecidableEq V] in
theorem finrank_image (f : U →ₗ[K] U') (hf : Function.Injective f) (M : Submodule K U) :
    Module.finrank K (M.map f) = Module.finrank K M :=
  (Submodule.equivMapOfInjective f hf M).finrank_eq.symm

variable [AddCommGroup T] [Module K T]

omit [Fintype V] [DecidableEq V] in
theorem projection_image_injective (f : U →ₗ[K] U') (hf : Function.Injective f) (M : Submodule K U)
    (g : U →ₗ[K] T) (g' : U' →ₗ[K] T) (hcomp : g'.comp f = g) (hg : Function.Injective g) :
    Function.Injective (g'.comp (M.map f).subtype) := by
  let e := Submodule.equivMapOfInjective f hf M
  intro a b hab
  obtain ⟨u, rfl⟩ := e.surjective a
  obtain ⟨v, rfl⟩ := e.surjective b
  have huv : u = v := by
    apply Subtype.ext
    apply hg
    have h : g' (f u.val) = g' (f v.val) := by
      simpa only [e, LinearMap.comp_apply, Submodule.subtype_apply, Submodule.coe_equivMapOfInjective_apply] using hab
    exact (LinearMap.congr_fun hcomp u.val).symm.trans (h.trans (LinearMap.congr_fun hcomp v.val))
  exact congrArg e huv

end PaperP1.RecoveryImage
