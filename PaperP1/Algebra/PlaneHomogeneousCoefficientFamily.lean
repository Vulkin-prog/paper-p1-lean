module

public import PaperP1.Algebra.HomogeneousMonomialCount
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # Literal three-coordinate homogeneous coefficient families for actual plane curves -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PlaneHomogeneousCoefficientFamily

open MvPolynomial Finset
open scoped Classical

abbrev Index (d : ℕ) := {m : Fin 3 →₀ ℕ // m.degree = d}

instance indexFinite (d : ℕ) : Finite (Index d) :=
  HomogeneousMonomialCount.exponent_finite (Fin 3) d

instance indexFintype (d : ℕ) : Fintype (Index d) := Fintype.ofFinite (Index d)

variable {R : Type*} [CommRing R]

def polynomial (d : ℕ) (w : Index d → R) : MvPolynomial (Fin 3) R :=
  ∑ m, monomial m.val (w m)

theorem coeff_index (d : ℕ) (w : Index d → R) (m : Index d) :
    (polynomial d w).coeff m.val = w m := by
  simp [polynomial, Subtype.val_injective.eq_iff]

theorem homogeneous (d : ℕ) (w : Index d → R) : (polynomial d w).IsHomogeneous d := by
  apply IsHomogeneous.sum
  intro m _
  exact isHomogeneous_monomial (w m) m.property

theorem map_polynomial {S : Type*} [CommRing S] (φ : R →+* S) (d : ℕ) (w : Index d → R) :
    map φ (polynomial d w) = polynomial d (fun m ↦ φ (w m)) := by
  simp only [polynomial, map_sum, map_monomial]

theorem nonzero (d : ℕ) (w : Index d → R) (hw : w ≠ 0) : polynomial d w ≠ 0 := by
  intro hz
  apply hw
  funext m
  have he := congrArg (fun P : MvPolynomial (Fin 3) R ↦ P.coeff m.val) hz
  simpa [coeff_index] using he

end PaperP1.PlaneHomogeneousCoefficientFamily
