module

public import PaperP1.Algebra.LastChartPolynomial
public import PaperP1.Algebra.GradedDehomogenizationQuotient
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # The actual last affine chart is the literal quotient by the last variable minus one -/

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.LastChartQuotient
open MvPolynomial
variable {R : Type*} [CommRing R] (n : ℕ)

def sectionMap : MvPolynomial (Fin n) R →+* MvPolynomial (Fin (n+1)) R :=
  (rename Fin.castSucc).toRingHom

theorem dehom_section : (PaperP1.LastChartPolynomial.dehomogenize (R := R) (n := n)).comp (sectionMap n) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [sectionMap, PaperP1.LastChartPolynomial.dehomogenize]
  · intro i
    simp [sectionMap, PaperP1.LastChartPolynomial.dehomogenize]

theorem surjective : Function.Surjective (PaperP1.LastChartPolynomial.dehomogenize (R := R) (n := n)) := by
  intro P
  exact ⟨sectionMap n P, RingHom.congr_fun (dehom_section n) P⟩

theorem kernel : RingHom.ker (PaperP1.LastChartPolynomial.dehomogenize (R := R) (n := n)) =
    Ideal.span ({X (Fin.last n) - 1} : Set (MvPolynomial (Fin (n+1)) R)) := by
  let I : Ideal (MvPolynomial (Fin (n+1)) R) := Ideal.span {X (Fin.last n)-1}
  let q := Ideal.Quotient.mk I
  have hz : q (X (Fin.last n)) = 1 := by
    have hh := Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_span_singleton_self ((X (Fin.last n) : MvPolynomial (Fin (n+1)) R)-1))
    change q (X (Fin.last n)-1) = 0 at hh
    simpa only [map_sub, map_one, sub_eq_zero] using hh
  have he : q.comp ((sectionMap n).comp PaperP1.LastChartPolynomial.dehomogenize) = q := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [sectionMap, PaperP1.LastChartPolynomial.dehomogenize]
    · intro i
      cases i using Fin.lastCases with
      | last => simp [sectionMap, PaperP1.LastChartPolynomial.dehomogenize, hz]
      | cast i => simp [sectionMap, PaperP1.LastChartPolynomial.dehomogenize]
  apply le_antisymm
  · intro P hP
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hh := RingHom.congr_fun he P
    change q (sectionMap n (PaperP1.LastChartPolynomial.dehomogenize P)) = q P at hh
    rw [RingHom.mem_ker.mp hP, map_zero, map_zero] at hh
    exact hh.symm
  · rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
    rw [map_sub, map_one]
    simp only [PaperP1.LastChartPolynomial.dehomogenize, coe_eval₂Hom, eval₂_X,
      Fin.snoc_last, sub_self]

def quotientEquiv : MvPolynomial (Fin (n+1)) R ⧸
    Ideal.span ({X (Fin.last n)-1} : Set (MvPolynomial (Fin (n+1)) R)) ≃+* MvPolynomial (Fin n) R :=
  (Ideal.quotEquivOfEq (kernel n).symm).trans
    ((PaperP1.LastChartPolynomial.dehomogenize (R := R) (n := n)).quotientKerEquivOfSurjective (surjective n))

theorem quotientEquiv_mk (P : MvPolynomial (Fin (n+1)) R) :
    quotientEquiv n (Ideal.Quotient.mk _ P) = PaperP1.LastChartPolynomial.dehomogenize P := by
  rw [quotientEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]

section Field
variable {F : Type*} [Field F]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem variable_mem : (X (Fin.last n) : MvPolynomial (Fin (n+1)) F) ∈
    homogeneousSubmodule (Fin (n+1)) F 1 := isHomogeneous_X F (Fin.last n)

def originalEquiv : HomogeneousLocalization.Away (homogeneousSubmodule (Fin (n+1)) F) (X (Fin.last n)) ≃+*
    MvPolynomial (Fin n) F :=
  (PaperP1.GradedDehomogenizationQuotient.equiv (homogeneousSubmodule (Fin (n+1)) F)
    (variable_mem n)).symm.trans (quotientEquiv n)

theorem originalEquiv_dehomogenization (P : MvPolynomial (Fin (n+1)) F) :
    originalEquiv n (PaperP1.GradedDehomogenization.map (homogeneousSubmodule (Fin (n+1)) F)
      (variable_mem n) P) = PaperP1.LastChartPolynomial.dehomogenize P := by
  change quotientEquiv n ((PaperP1.GradedDehomogenizationQuotient.equiv
    (homogeneousSubmodule (Fin (n+1)) F) (variable_mem n)).symm
    (PaperP1.GradedDehomogenization.map (homogeneousSubmodule (Fin (n+1)) F)
      (variable_mem n) P)) = _
  rw [← PaperP1.GradedDehomogenizationQuotient.equiv_mk, RingEquiv.symm_apply_apply]
  exact quotientEquiv_mk n P
end Field

end PaperP1.LastChartQuotient
