module

public import PaperP1.Algebra.P3GraphPlaneSection

/-! # Exact coefficient polynomials and reconstruction of actual graph-plane sections -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3GraphPlaneSectionCoefficients

open MvPolynomial PlaneHomogeneousCoefficientFamily P3GraphPlaneSection

variable {F : Type*} [CommRing F]

def coefficients (d : ℕ) (P : MvPolynomial (Fin 4) F) : Index d → MvPolynomial (Fin 3) F :=
  fun m ↦ (universalSection F P).coeff m.val

theorem degree_bound (d : ℕ) (P : MvPolynomial (Fin 4) F) (hP : P.IsHomogeneous d) (m : Index d) :
    (coefficients d P m).totalDegree ≤ d := homogeneous_parameter_degree P hP m.val

theorem specialized_coefficient {K : Type*} [CommRing K] (φ : F →+* K) (a : Fin 3 → K)
    (d : ℕ) (P : MvPolynomial (Fin 4) F) (m : Index d) :
    eval₂Hom φ a (coefficients d P m) = (planeSection a (map φ P)).coeff m.val := by
  have he := congrArg (fun Q : MvPolynomial (Fin 3) K ↦ Q.coeff m.val) (evaluate_universal φ a P)
  exact he

theorem specialized_polynomial {K : Type*} [CommRing K] (φ : F →+* K) (a : Fin 3 → K)
    (d : ℕ) (P : MvPolynomial (Fin 4) F) (hP : P.IsHomogeneous d) :
    polynomial d (fun m ↦ eval₂Hom φ a (coefficients d P m)) = planeSection a (map φ P) := by
  have he : (fun m ↦ eval₂Hom φ a (coefficients d P m)) =
      (fun m : Index d ↦ (planeSection a (map φ P)).coeff m.val) :=
    funext (specialized_coefficient φ a d P)
  rw [he]
  exact PlaneHomogeneousReconstruction.reconstruct d _ (section_homogeneous a _ (hP.map φ))

theorem evaluation_polynomial (a : Fin 3 → F) (d : ℕ) (P : MvPolynomial (Fin 4) F)
    (hP : P.IsHomogeneous d) :
    polynomial d (fun m ↦ eval a (coefficients d P m)) = planeSection a P := by
  simpa only [eval, map_id] using specialized_polynomial (RingHom.id F) a d P hP

end PaperP1.P3GraphPlaneSectionCoefficients
