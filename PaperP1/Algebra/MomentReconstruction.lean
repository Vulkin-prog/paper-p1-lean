module

public import PaperP1.Algebra.FiniteExpectation

/-! # The exact reconstruction of an uncentered moment from heterogeneous centered moments -/

set_option autoImplicit false

@[expose] public section

namespace PaperP1.MomentReconstruction

open Finset PaperP1.Algebra

theorem finite_uncentered_expansion {Ω ι R : Type*} [Fintype Ω] [DecidableEq ι] [CommRing R]
    (w : Ω → R) (J : ι → Ω → R) (p : ι → R) (I : Finset ι) :
    finiteExpectation w (fun ω ↦ ∏ x ∈ I, J x ω) =
      ∑ A ∈ I.powerset, centeredMoment w J p A * ∏ x ∈ I \ A, p x := by
  have h := finite_weighted_product_expansion I (RingHom.id R) w p (fun x ω ↦ J x ω - p x) 1
  simp only [RingHom.id_apply, mul_one, one_pow] at h
  have hprod (ω : Ω) : (∏ x ∈ I, (p x + (J x ω - p x))) = ∏ x ∈ I, J x ω := by
    apply prod_congr rfl
    intro x _hx
    rw [add_comm, sub_add_cancel]
  simp_rw [hprod] at h
  exact h

end PaperP1.MomentReconstruction
