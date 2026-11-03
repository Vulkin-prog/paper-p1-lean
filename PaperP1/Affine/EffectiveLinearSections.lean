module

public import PaperP1.Affine.TwoTargetKernel

/-! # Effective source and target spaces have exact linear lifts without local regularity -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.EffectiveLinearSections

variable {K U P : Type*} [Field K] [AddCommGroup U] [Module K U]
  [AddCommGroup P] [Module K P]

theorem exists_section (q : P →ₗ[K] U) (W : Submodule K U) (hW : W ≤ LinearMap.range q) :
    ∃ σ : W →ₗ[K] P, q.comp σ = W.subtype ∧ Function.Injective σ := by
  obtain ⟨r, hr⟩ := q.rangeRestrict.exists_rightInverse_of_surjective q.range_rangeRestrict
  let σ := r.comp (Submodule.inclusion hW)
  have hσ : q.comp σ = W.subtype := by
    ext w
    exact congrArg Subtype.val (LinearMap.congr_fun hr (Submodule.inclusion hW w))
  refine ⟨σ, hσ, ?_⟩
  intro w z hwz
  apply Subtype.ext
  have heq := congrArg q hwz
  change (q.comp σ) w = (q.comp σ) z at heq
  simpa only [hσ, Submodule.subtype_apply] using heq

variable {PY PZ : Type*} [AddCommGroup PY] [Module K PY] [AddCommGroup PZ] [Module K PZ]

def relationLift (W Y Z : Submodule K U) (σW : W →ₗ[K] P) (σY : Y →ₗ[K] PY) (σZ : Z →ₗ[K] PZ) :
    TwoTargetKernel.Kernel W Y Z →ₗ[K] (P × PY × PZ) :=
  (σW.prodMap (σY.prodMap σZ)).comp (TwoTargetKernel.Kernel W Y Z).subtype

theorem relation_lift_equation (W Y Z : Submodule K U)
    (qW : P →ₗ[K] U) (qY : PY →ₗ[K] U) (qZ : PZ →ₗ[K] U)
    (σW : W →ₗ[K] P) (σY : Y →ₗ[K] PY) (σZ : Z →ₗ[K] PZ)
    (hW : qW.comp σW = W.subtype) (hY : qY.comp σY = Y.subtype) (hZ : qZ.comp σZ = Z.subtype)
    (r : TwoTargetKernel.Kernel W Y Z) :
    qW (relationLift W Y Z σW σY σZ r).1 +
      qY (relationLift W Y Z σW σY σZ r).2.1 +
      qZ (relationLift W Y Z σW σY σZ r).2.2 = 0 := by
  change (qW.comp σW) r.val.1 + (qY.comp σY) r.val.2.1 + (qZ.comp σZ) r.val.2.2 = 0
  rw [hW, hY, hZ]
  exact r.property

theorem left_lift_injective (W Y Z : Submodule K U)
    (σY : Y →ₗ[K] PY) (hY : Function.Injective σY) (hWZ : Disjoint W Z) :
    Function.Injective (σY.comp (TwoTargetKernel.leftProjection W Y Z)) :=
  hY.comp (TwoTargetKernel.left_projection_injective W Y Z hWZ)

theorem right_lift_injective (W Y Z : Submodule K U)
    (σZ : Z →ₗ[K] PZ) (hZ : Function.Injective σZ) (hWY : Disjoint W Y) :
    Function.Injective (σZ.comp (TwoTargetKernel.rightProjection W Y Z)) :=
  hZ.comp (TwoTargetKernel.right_projection_injective W Y Z hWY)

end PaperP1.EffectiveLinearSections
