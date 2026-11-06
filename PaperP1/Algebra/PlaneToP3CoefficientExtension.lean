module

public import PaperP1.Algebra.PlaneHomogeneousCoefficientFamily
public import PaperP1.Algebra.P3HomogeneousCoefficientFamily

/-! # Exact universal integer coefficient substitution from plane curves to four-coordinate equations -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PlaneToP3CoefficientExtension

open MvPolynomial Finset
open scoped Classical

def coefficientForm (d : ℕ) (m : P3HomogeneousCoefficientFamily.Index d) :
    MvPolynomial (PlaneHomogeneousCoefficientFamily.Index d) ℤ :=
  ∑ n, if Finsupp.mapDomain Fin.succ n.val = m.val then X n else 0

def pullback (d : ℕ) : MvPolynomial (P3HomogeneousCoefficientFamily.Index d) ℤ →+*
    MvPolynomial (PlaneHomogeneousCoefficientFamily.Index d) ℤ := eval₂Hom C (coefficientForm d)

theorem form_homogeneous (d : ℕ) (m : P3HomogeneousCoefficientFamily.Index d) :
    (coefficientForm d m).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro n _
  split_ifs
  · exact isHomogeneous_X ℤ n
  · exact isHomogeneous_zero _ _ _

theorem evaluate_form {F : Type*} [CommRing F] (d : ℕ)
    (w : PlaneHomogeneousCoefficientFamily.Index d → F) (m : P3HomogeneousCoefficientFamily.Index d) :
    eval w (map (Int.castRingHom F) (coefficientForm d m)) =
      ∑ n, if Finsupp.mapDomain Fin.succ n.val = m.val then w n else 0 := by
  simp only [coefficientForm, map_sum]
  apply sum_congr rfl
  intro n _
  split_ifs <;> simp

theorem extended_coefficient {F : Type*} [CommRing F] (d : ℕ)
    (w : PlaneHomogeneousCoefficientFamily.Index d → F) (m : P3HomogeneousCoefficientFamily.Index d) :
    (rename Fin.succ (PlaneHomogeneousCoefficientFamily.polynomial d w)).coeff m.val =
      ∑ n, if Finsupp.mapDomain Fin.succ n.val = m.val then w n else 0 := by
  simp only [PlaneHomogeneousCoefficientFamily.polynomial, map_sum, rename_monomial, coeff_sum,
    coeff_monomial]

theorem extended_homogeneous {F : Type*} [CommRing F] (d : ℕ)
    (w : PlaneHomogeneousCoefficientFamily.Index d → F) :
    (rename Fin.succ (PlaneHomogeneousCoefficientFamily.polynomial d w)).IsHomogeneous d :=
  (PlaneHomogeneousCoefficientFamily.homogeneous d w).rename_isHomogeneous

theorem reconstruct_extended {F : Type*} [CommRing F] (d : ℕ)
    (w : PlaneHomogeneousCoefficientFamily.Index d → F) :
    P3HomogeneousCoefficientFamily.polynomial d (fun m ↦
      (rename Fin.succ (PlaneHomogeneousCoefficientFamily.polynomial d w)).coeff m.val) =
        rename Fin.succ (PlaneHomogeneousCoefficientFamily.polynomial d w) :=
  P3HomogeneousCoefficientFamily.reconstruct d _ (extended_homogeneous d w)

theorem pullback_homogeneous (d : ℕ) (P : MvPolynomial (P3HomogeneousCoefficientFamily.Index d) ℤ)
    {n : ℕ} (hP : P.IsHomogeneous n) : (pullback d P).IsHomogeneous n := by
  have hh := hP.eval₂ C (coefficientForm d) (fun r ↦ isHomogeneous_C _ r) (form_homogeneous d)
  simpa only [pullback, coe_eval₂Hom, one_mul] using hh

theorem evaluate_pullback {F : Type*} [CommRing F] (d : ℕ)
    (w : PlaneHomogeneousCoefficientFamily.Index d → F)
    (P : MvPolynomial (P3HomogeneousCoefficientFamily.Index d) ℤ) :
    eval w (map (Int.castRingHom F) (pullback d P)) =
      eval (fun m ↦ (rename Fin.succ (PlaneHomogeneousCoefficientFamily.polynomial d w)).coeff m.val)
        (map (Int.castRingHom F) P) := by
  have he : (eval₂Hom (Int.castRingHom F) w).comp (pullback d) =
      eval₂Hom (Int.castRingHom F)
        (fun m ↦ (rename Fin.succ (PlaneHomogeneousCoefficientFamily.polynomial d w)).coeff m.val) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [pullback]
    · intro m
      simp only [RingHom.comp_apply, pullback, eval₂Hom_X']
      simpa only [eval_map, coe_eval₂Hom] using
        (evaluate_form d w m).trans (extended_coefficient d w m).symm
  simpa only [RingHom.comp_apply, eval_map, coe_eval₂Hom] using RingHom.congr_fun he P

end PaperP1.PlaneToP3CoefficientExtension
