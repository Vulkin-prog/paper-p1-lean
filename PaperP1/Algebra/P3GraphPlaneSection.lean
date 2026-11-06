module

public import PaperP1.Algebra.NestedPolynomialCoefficientDegree
public import PaperP1.Algebra.PolynomialSubstitutionDegree
public import PaperP1.Algebra.PlaneHomogeneousReconstruction

/-! # Literal projective graph-plane sections and their universal parameter coefficient polynomials -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3GraphPlaneSection

open MvPolynomial Finset
open scoped Classical

variable {F : Type*} [CommRing F]

def form (a : Fin 3 → F) : MvPolynomial (Fin 3) F := ∑ i, C (a i) * X i

def coordinates (a : Fin 3 → F) : Fin 4 → MvPolynomial (Fin 3) F := Fin.cons (form a) X

def planeSection (a : Fin 3 → F) : MvPolynomial (Fin 4) F →+* MvPolynomial (Fin 3) F :=
  eval₂Hom C (coordinates a)

def universalForm (F : Type*) [CommRing F] : MvPolynomial (Fin 3) (MvPolynomial (Fin 3) F) :=
  ∑ i, C (X i) * X i

def universalCoordinates (F : Type*) [CommRing F] :
    Fin 4 → MvPolynomial (Fin 3) (MvPolynomial (Fin 3) F) :=
  Fin.cons (universalForm F) X

def universalSection (F : Type*) [CommRing F] :
    MvPolynomial (Fin 4) F →+* MvPolynomial (Fin 3) (MvPolynomial (Fin 3) F) :=
  eval₂Hom (C.comp C) (universalCoordinates F)

def dualCoordinates (F : Type*) [CommRing F] :
    Fin 4 → MvPolynomial (Fin 3) (MvPolynomial (Fin 3) F) :=
  Fin.cons (universalForm F) (fun i ↦ C (X i))

theorem form_homogeneous (a : Fin 3 → F) : (form a).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro i _
  exact isHomogeneous_C_mul_X (a i) i

theorem coordinates_homogeneous (a : Fin 3 → F) (i : Fin 4) : (coordinates a i).IsHomogeneous 1 := by
  cases i using Fin.cases with
  | zero => exact form_homogeneous a
  | succ i => exact isHomogeneous_X F i

theorem section_homogeneous (a : Fin 3 → F) (P : MvPolynomial (Fin 4) F) {d : ℕ}
    (hP : P.IsHomogeneous d) : (planeSection a P).IsHomogeneous d := by
  have hh := hP.eval₂ C (coordinates a) (fun r ↦ isHomogeneous_C _ r) (coordinates_homogeneous a)
  simpa only [planeSection, coe_eval₂Hom, one_mul] using hh

theorem universalForm_homogeneous : (universalForm F).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro i _
  exact isHomogeneous_C_mul_X (X i) i

theorem universalCoordinates_homogeneous (i : Fin 4) : (universalCoordinates F i).IsHomogeneous 1 := by
  cases i using Fin.cases with
  | zero => exact universalForm_homogeneous
  | succ i => exact isHomogeneous_X _ i

theorem universal_homogeneous (P : MvPolynomial (Fin 4) F) {d : ℕ} (hP : P.IsHomogeneous d) :
    (universalSection F P).IsHomogeneous d := by
  have hh := hP.eval₂ (C.comp C) (universalCoordinates F)
    (fun r ↦ isHomogeneous_C _ (C r)) universalCoordinates_homogeneous
  simpa only [universalSection, coe_eval₂Hom, one_mul] using hh

theorem commute_universal (P : MvPolynomial (Fin 4) F) :
    commAlgEquiv F (Fin 3) (Fin 3) (universalSection F P) =
      eval₂Hom (C.comp C) (dualCoordinates F) P := by
  have he : (commAlgEquiv F (Fin 3) (Fin 3)).toRingHom.comp (universalSection F) =
      eval₂Hom (C.comp C) (dualCoordinates F) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [universalSection]
    · intro i
      cases i using Fin.cases <;>
        simp [universalSection, universalCoordinates, dualCoordinates, universalForm,
          mul_comm]
  exact RingHom.congr_fun he P

theorem dual_degree_le (i : Fin 4) : (dualCoordinates F i).totalDegree ≤ 1 := by
  cases i using Fin.cases with
  | zero => exact universalForm_homogeneous.totalDegree_le
  | succ i => simp [dualCoordinates]

theorem parameter_degree (P : MvPolynomial (Fin 4) F) (m : Fin 3 →₀ ℕ) :
    ((universalSection F P).coeff m).totalDegree ≤ P.totalDegree := by
  apply (NestedPolynomialCoefficientDegree.coefficient_degree_le _ m).trans
  rw [commute_universal]
  simpa only [one_mul] using PolynomialSubstitutionDegree.eval2_bound
    (C : F →+* MvPolynomial (Fin 3) F) (dualCoordinates F) 1 dual_degree_le P

theorem homogeneous_parameter_degree (P : MvPolynomial (Fin 4) F) {d : ℕ}
    (hP : P.IsHomogeneous d) (m : Fin 3 →₀ ℕ) :
    ((universalSection F P).coeff m).totalDegree ≤ d :=
  (parameter_degree P m).trans hP.totalDegree_le

theorem evaluate_universal {K : Type*} [CommRing K] (φ : F →+* K) (a : Fin 3 → K)
    (P : MvPolynomial (Fin 4) F) :
    map (eval₂Hom φ a) (universalSection F P) = planeSection a (map φ P) := by
  have he : (MvPolynomial.map (eval₂Hom φ a)).comp (universalSection F) =
      (planeSection a).comp (MvPolynomial.map φ) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [universalSection, planeSection]
    · intro i
      cases i using Fin.cases <;>
        simp [universalSection, universalCoordinates, universalForm, planeSection, coordinates, form]
  exact RingHom.congr_fun he P

end PaperP1.P3GraphPlaneSection
