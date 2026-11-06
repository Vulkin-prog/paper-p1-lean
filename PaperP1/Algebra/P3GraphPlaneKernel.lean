module

public import PaperP1.Algebra.P3GraphPlaneSection
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.Algebra.MvPolynomial.Nilpotent
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-! # A graph-plane section vanishes identically exactly when its actual linear equation divides the original polynomial -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3GraphPlaneKernel

open MvPolynomial P3GraphPlaneSection

variable {F : Type*} [Field F]

def equation (a : Fin 3 → F) : MvPolynomial (Fin 4) F := X 0 - rename Fin.succ (form a)

theorem equivalence_rename (P : MvPolynomial (Fin 3) F) :
    finSuccEquiv F 3 (rename Fin.succ P) = Polynomial.C P := by
  have he : (finSuccEquiv F 3).toRingHom.comp (rename Fin.succ).toRingHom = Polynomial.C := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [finSuccEquiv_apply]
    · intro i
      simp [finSuccEquiv_apply]
  exact RingHom.congr_fun he P

theorem equivalence_equation (a : Fin 3 → F) :
    finSuccEquiv F 3 (equation a) = Polynomial.X - Polynomial.C (form a) := by
  rw [equation, map_sub, finSuccEquiv_X_zero, equivalence_rename]

theorem section_as_univariate_evaluation (a : Fin 3 → F) (P : MvPolynomial (Fin 4) F) :
    planeSection a P = Polynomial.eval (form a) (finSuccEquiv F 3 P) := by
  have he : planeSection a = (Polynomial.evalRingHom (form a)).comp (finSuccEquiv F 3).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [planeSection, finSuccEquiv_apply]
    · intro i
      cases i using Fin.cases <;>
        simp [planeSection, coordinates, finSuccEquiv_apply]
  exact RingHom.congr_fun he P

theorem zero_iff_dvd (a : Fin 3 → F) (P : MvPolynomial (Fin 4) F) :
    planeSection a P = 0 ↔ equation a ∣ P := by
  rw [section_as_univariate_evaluation]
  have he : equation a ∣ P ↔ (Polynomial.X - Polynomial.C (form a)) ∣ finSuccEquiv F 3 P := by
    constructor
    · intro hd
      have hh := map_dvd (finSuccEquiv F 3).toRingHom hd
      change finSuccEquiv F 3 (equation a) ∣ finSuccEquiv F 3 P at hh
      rw [equivalence_equation] at hh
      exact hh
    · intro hd
      have hh := map_dvd (finSuccEquiv F 3).symm.toRingHom hd
      have ha : (finSuccEquiv F 3).symm (Polynomial.X - Polynomial.C (form a)) = equation a := by
        apply (finSuccEquiv F 3).injective
        rw [AlgEquiv.apply_symm_apply, equivalence_equation]
      change (finSuccEquiv F 3).symm (Polynomial.X - Polynomial.C (form a)) ∣
        (finSuccEquiv F 3).symm (finSuccEquiv F 3 P) at hh
      rw [ha, AlgEquiv.symm_apply_apply] at hh
      exact hh
  rw [he, Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def]

theorem equation_irreducible (a : Fin 3 → F) : Irreducible (equation a) := by
  apply (MulEquiv.irreducible_iff (finSuccEquiv F 3)).mp
  rw [equivalence_equation]
  exact Polynomial.irreducible_X_sub_C _

theorem equation_homogeneous (a : Fin 3 → F) : (equation a).IsHomogeneous 1 :=
  (isHomogeneous_X F 0).sub (form_homogeneous a).rename_isHomogeneous

theorem section_ne_zero (P : MvPolynomial (Fin 4) F) {d : ℕ} (hd : 1 < d)
    (hP : P.IsHomogeneous d) (hirr : Irreducible P) (a : Fin 3 → F) : planeSection a P ≠ 0 := by
  intro hz
  obtain ⟨Q, hQ⟩ := (zero_iff_dvd a P).mp hz
  have heq := equation_irreducible a
  have hunit := (hirr.isUnit_or_isUnit hQ).resolve_left heq.not_isUnit
  have hdegree := totalDegree_mul_of_isDomain heq.ne_zero hunit.ne_zero
  rw [← hQ, hP.totalDegree hirr.ne_zero, (equation_homogeneous a).totalDegree heq.ne_zero,
    (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hunit).2] at hdegree
  omega

end PaperP1.P3GraphPlaneKernel
