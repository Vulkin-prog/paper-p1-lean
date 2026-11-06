module

public import PaperP1.Algebra.P3HomogeneousCoefficientFamily

/-! # Exact coefficient-field transport of the actual original homogeneous equation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3CoefficientFieldTransport

open MvPolynomial P3HomogeneousCoefficientFamily

variable {R S : Type*} [CommRing R] [CommRing S]

theorem map_polynomial (φ : R →+* S) (d : ℕ) (w : Index d → R) :
    map φ (polynomial d w) = polynomial d (fun m ↦ φ (w m)) := by
  simp only [polynomial, map_sum, map_monomial]

theorem map_reconstruct (φ : R →+* S) (d : ℕ) (P : MvPolynomial (Fin 4) R) (hP : P.IsHomogeneous d) :
    map φ P = polynomial d (fun m ↦ φ (P.coeff m.val)) := by
  have hh := map_polynomial φ d (fun m : Index d ↦ P.coeff m.val)
  rw [reconstruct d P hP] at hh
  exact hh

end PaperP1.P3CoefficientFieldTransport
