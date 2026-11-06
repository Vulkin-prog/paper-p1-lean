module

public import PaperP1.Algebra.PlaneHomogeneousCoefficientFamily

/-! # Exact reconstruction of every actual homogeneous plane equation from its indexed coefficients -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PlaneHomogeneousReconstruction

open MvPolynomial PlaneHomogeneousCoefficientFamily
open scoped Classical

variable {R : Type*} [CommRing R]

theorem coeff_outside (d : ℕ) (w : Index d → R) (m : Fin 3 →₀ ℕ) (hm : m.degree ≠ d) :
    (polynomial d w).coeff m = 0 := by
  have hne (s : Index d) : s.val ≠ m := by intro he; exact hm (he ▸ s.property)
  simp only [polynomial, coeff_sum, coeff_monomial, ite_eq_right (hne _), Finset.sum_const_zero]

theorem reconstruct (d : ℕ) (P : MvPolynomial (Fin 3) R) (hP : P.IsHomogeneous d) :
    polynomial d (fun m ↦ P.coeff m.val) = P := by
  ext m
  by_cases hm : m.degree = d
  · exact coeff_index d (fun m ↦ P.coeff m.val) ⟨m, hm⟩
  · rw [coeff_outside d _ m hm]
    apply Eq.symm
    by_contra hc
    apply hm
    have he := hP.degree_eq_sum_deg_support (mem_support_iff.mpr hc)
    simpa only [Finsupp.degree_apply] using he.symm

end PaperP1.PlaneHomogeneousReconstruction
