module

public import PaperP1.Arithmetic.ProjectiveFactorCoefficients
public import Mathlib.Algebra.MvPolynomial.Equiv

/-! # Absolute projective irreducibility is transported by the actual pair exchange -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GeometricFactorSwap

open Polynomial PaperP1.IntegerFactorProjectiveCurve

def complexProjective (G : ℤ[X][X]) : MvPolynomial (Fin 2) (MvPolynomial (Fin 2) ℂ) :=
  MvPolynomial.map (MvPolynomial.map (σ := Fin 2) (Int.castRingHom ℂ)) (projective G)

def Geometric (G : ℤ[X][X]) : Prop := Irreducible (complexProjective G)

theorem comm_coefficient {R : Type*} [CommSemiring R]
    (P : MvPolynomial (Fin 2) (MvPolynomial (Fin 2) R)) (m n : Fin 2 →₀ ℕ) :
    ((MvPolynomial.commAlgEquiv R (Fin 2) (Fin 2) P).coeff m).coeff n = (P.coeff n).coeff m := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hP, hQ]
  | monomial i p =>
    induction p using MvPolynomial.induction_on' with
    | add p q hp hq => simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq]
    | monomial j r =>
      have he : MvPolynomial.commAlgEquiv R (Fin 2) (Fin 2)
          (MvPolynomial.monomial i (MvPolynomial.monomial j r)) =
          MvPolynomial.monomial j (MvPolynomial.monomial i r) :=
        AddMonoidAlgebra.commAlgEquiv_single_single i j r
      rw [he]
      by_cases hi : i = n <;> by_cases hj : j = m <;> simp [hi, hj]

theorem complex_coefficient (G : ℤ[X][X]) (m n : Fin 2 →₀ ℕ) :
    ((complexProjective G).coeff m).coeff n = (((projective G).coeff m).coeff n : ℂ) := by
  unfold complexProjective
  change ((MvPolynomial.map (Int.castRingHom ℂ) ((projective G).coeff m)).coeff n) = _
  exact MvPolynomial.coeff_map (Int.castRingHom ℂ) ((projective G).coeff m) n

theorem complex_projective_swap (G : ℤ[X][X]) :
    complexProjective (Bivariate.swap G) = MvPolynomial.commAlgEquiv ℂ (Fin 2) (Fin 2) (complexProjective G) := by
  apply MvPolynomial.ext
  intro m
  apply MvPolynomial.ext
  intro n
  rw [complex_coefficient, comm_coefficient, complex_coefficient, ProjectiveFactorCoefficients.projective_coefficient_swap]

theorem geometric_swap_iff (G : ℤ[X][X]) : Geometric (Bivariate.swap G) ↔ Geometric G := by
  unfold Geometric
  rw [complex_projective_swap]
  exact MulEquiv.irreducible_iff (MvPolynomial.commAlgEquiv ℂ (Fin 2) (Fin 2))

theorem geometric_swap (G : ℤ[X][X]) (hG : Geometric G) : Geometric (Bivariate.swap G) :=
  (geometric_swap_iff G).mpr hG

end PaperP1.GeometricFactorSwap
