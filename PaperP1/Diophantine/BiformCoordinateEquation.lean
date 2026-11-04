module

public import PaperP1.Diophantine.BiformLinearCoordinates
public import PaperP1.Algebra.BivariateReciprocalProduct

/-! # Actual nonzero integer biforms in the transformed pair coordinates -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BiformCoordinateEquation

open PaperP1.HomogeneousCharts PaperP1.BiformLinearCoordinates
open PaperP1.DeterminantAuxiliaryBiform PaperP1.DeterminantIntegerRows
open PaperP1.BiquadraticCoefficientPolynomials

variable {a b : ℕ}

def weights (F : Fin (a + 1) → MvPolynomial (Fin 2) ℤ) : Exponent a b → ℤ :=
  fun i ↦ (chart (F i.1)).coeff i.2.val

theorem forms_weights (F : Fin (a + 1) → MvPolynomial (Fin 2) ℤ)
    (hF : ∀ i, (F i).IsHomogeneous b) (i : Fin (a + 1)) :
    forms a b (weights F) i = F i := by
  unfold forms weights
  rw [PaperP1.BivariateReciprocalProduct.row_reconstruction (chart (F i)) b (chart_degree _ (hF i))]
  exact chart_homogenize _ (hF i)

def equation (F : Fin (a + 1) → MvPolynomial (Fin 2) ℤ) :
    MvPolynomial (Fin 2) (MvPolynomial (Fin 2) ℤ) := biform a b (weights F)

theorem weights_nonzero (F : Fin (a + 1) → MvPolynomial (Fin 2) ℤ)
    (hF : ∀ i, (F i).IsHomogeneous b) (hF0 : F ≠ 0) : weights (b := b) F ≠ 0 := by
  intro hz
  apply hF0
  funext i
  rw [← forms_weights F hF i, hz]
  simp [forms, row]

theorem equation_nonzero (F : Fin (a + 1) → MvPolynomial (Fin 2) ℤ)
    (hF : ∀ i, (F i).IsHomogeneous b) (hF0 : F ≠ 0) : equation (b := b) F ≠ 0 :=
  biform_nonzero a b _ (weights_nonzero F hF hF0)

theorem equation_homogeneous (F : Fin (a + 1) → MvPolynomial (Fin 2) ℤ) :
    (equation (b := b) F).IsHomogeneous a := biform_homogeneous a b _

theorem equation_evaluation (F : Fin (a + 1) → MvPolynomial (Fin 2) ℤ)
    (hF : ∀ i, (F i).IsHomogeneous b) (x y : Fin 2 → ℤ) :
    MvPolynomial.eval₂ (MvPolynomial.eval y) x (equation (b := b) F) =
      BidegreeOneElimination.original F x y := by
  rw [equation, biform_eval_original]
  congr 1
  funext i
  exact forms_weights F hF i

theorem equation_height (F : Fin (a + 1) → MvPolynomial (Fin 2) ℤ)
    (hF : ∀ i, (F i).IsHomogeneous b) (H : ℕ)
    (hH : ∀ i m, ((F i).coeff m).natAbs ≤ H) :
    ∀ m n, |((equation (b := b) F).coeff m).coeff n| ≤ (H : ℤ) := by
  apply biform_coefficient_bound a b H
  intro i
  have hj : i.2.val ≤ b := by have := i.2.isLt; omega
  have hc := hH i.1 (fun₀ | 0 => i.2.val | 1 => b - i.2.val)
  change |(chart (F i.1)).coeff i.2.val| ≤ (H : ℤ)
  rw [chart_coeff _ (hF i.1) i.2.val hj, ← Int.natCast_natAbs]
  exact_mod_cast hc

theorem transformed_equation_evaluation (A B : Matrix (Fin 2) (Fin 2) ℤ)
    (F : Fin (a + 1) → MvPolynomial (Fin 2) ℤ) (hF : ∀ i, (F i).IsHomogeneous b)
    (x y : Fin 2 → ℤ) :
    MvPolynomial.eval₂ (MvPolynomial.eval y) x (equation (b := b) (transform (b := b) A B F)) =
      BidegreeOneElimination.original F (A.mulVec x) (B.mulVec y) := by
  rw [equation_evaluation _ (transform_homogeneous A B F), transform_evaluation A B F hF]

theorem transformed_equation_nonzero (A A' B B' : Matrix (Fin 2) (Fin 2) ℤ)
    (hAA' : A * A' = 1) (hA'A : A' * A = 1) (hBB' : B * B' = 1) (hB'B : B' * B = 1)
    (F : Fin (a + 1) → MvPolynomial (Fin 2) ℤ)
    (hF : ∀ i, (F i).IsHomogeneous b) (hF0 : F ≠ 0) :
    equation (b := b) (transform (b := b) A B F) ≠ 0 :=
  equation_nonzero _ (transform_homogeneous A B F)
    (transform_nonzero A A' B B' hAA' hA'A hBB' hB'B F hF hF0)

theorem transformed_equation_height (A B : Matrix (Fin 2) (Fin 2) ℤ)
    (F : Fin (a + 1) → MvPolynomial (Fin 2) ℤ) (hF : ∀ i, (F i).IsHomogeneous b)
    (H M T : ℕ) (hH : ∀ i m, ((F i).coeff m).natAbs ≤ H)
    (hM : ∀ i j, (A i j).natAbs ≤ M) (hT : ∀ i j, (B i j).natAbs ≤ T) :
    ∀ m n, |((equation (b := b) (transform (b := b) A B F)).coeff m).coeff n| ≤
      (((b + 1) * ((a + 1) * H * (2 * M) ^ a) * (2 * T) ^ b : ℕ) : ℤ) :=
  equation_height _ (transform_homogeneous A B F) _ (transform_height A B F hF H M T hH hM hT)

end PaperP1.BiformCoordinateEquation
