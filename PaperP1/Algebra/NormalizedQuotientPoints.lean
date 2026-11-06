module

public import PaperP1.Algebra.GradedDehomogenizationQuotient

/-! # Actual normalized ring points are the points of the quotient by b-1 -/

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.NormalizedQuotientPoints
variable {A Ω : Type*} [CommRing A] [CommRing Ω]

def quotientEquiv (b : A) : {φ : A →+* Ω // φ b = 1} ≃
    (A ⧸ PaperP1.GradedDehomogenizationQuotient.ideal b →+* Ω) where
  toFun φ := Ideal.Quotient.lift _ φ.val (by
    change PaperP1.GradedDehomogenizationQuotient.ideal b ≤ RingHom.ker φ.val
    rw [PaperP1.GradedDehomogenizationQuotient.ideal, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
    rw [map_sub, map_one, φ.property, sub_self])
  invFun ψ := ⟨ψ.comp (Ideal.Quotient.mk _), by
    change ψ (Ideal.Quotient.mk _ b) = 1
    rw [PaperP1.GradedDehomogenizationQuotient.quotient_variable, map_one]⟩
  left_inv φ := by
    apply Subtype.ext
    apply RingHom.ext
    intro a
    rfl
  right_inv ψ := by
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro a
    rfl

def ringEquivPoints {B : Type*} [CommRing B] (e : A ≃+* B) : (A →+* Ω) ≃ (B →+* Ω) where
  toFun φ := φ.comp e.symm.toRingHom
  invFun ψ := ψ.comp e.toRingHom
  left_inv φ := by
    apply RingHom.ext
    intro a
    exact congrArg φ (e.symm_apply_apply a)
  right_inv ψ := by
    apply RingHom.ext
    intro b
    exact congrArg ψ (e.apply_symm_apply b)

end PaperP1.NormalizedQuotientPoints
