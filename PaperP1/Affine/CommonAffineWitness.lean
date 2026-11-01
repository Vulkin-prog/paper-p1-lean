module

public import PaperP1.Affine.PartitionMoments

/-! # A realizable family can use its common solution as every local affine witness -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.Affine

variable {V ι : Type*} [AddCommGroup V] [Module 𝔽₂ V]

theorem effectiveIndicator_eq_of_event (S : Submodule 𝔽₂ (V →ₗ[𝔽₂] 𝔽₂)) (a b : V)
    (hab : effectiveEvent S a b) (v : V) : effectiveIndicator S a v = effectiveIndicator S b v := by
  classical
  have hevent : effectiveEvent S a v ↔ effectiveEvent S b v := by
    constructor
    · intro hv s
      exact (hv s).trans (hab s).symm
    · intro hv s
      exact (hv s).trans (hab s)
  simp only [effectiveIndicator, hevent]

variable [Fintype V] [Fintype ι] [DecidableEq ι]
variable (S : ι → Submodule 𝔽₂ (V →ₗ[𝔽₂] 𝔽₂)) [∀ i, Fintype (S i)]

omit [DecidableEq ι] [∀ i, Fintype (S i)] in
theorem effectiveJointMoment_common_witness (a : ι → V) (b : V) (hab : ∀ i, effectiveEvent (S i) (a i) b) :
    effectiveJointMoment S a = effectiveJointMoment S (fun _ ↦ b) := by
  unfold effectiveJointMoment
  congr 1
  funext v
  exact Finset.prod_congr rfl (fun i _ ↦ effectiveIndicator_eq_of_event (S i) (a i) b (hab i) v)

omit [DecidableEq ι] in
theorem effectiveCenteredMoment_common_witness (a : ι → V) (b : V) (hab : ∀ i, effectiveEvent (S i) (a i) b) :
    effectiveCenteredMoment S a = effectiveCenteredMoment S (fun _ ↦ b) := by
  unfold effectiveCenteredMoment
  congr 1
  funext v
  apply Finset.prod_congr rfl
  intro i _
  rw [effectiveIndicator_eq_of_event (S i) (a i) b (hab i)]

end PaperP1.Affine
