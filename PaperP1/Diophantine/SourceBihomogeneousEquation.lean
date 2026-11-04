module

public import PaperP1.Diophantine.BiformPointCoordinates

/-! # The literal integer source equation of bidegree two-one and its exact coordinate values -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourceBihomogeneousEquation

open MvPolynomial PaperP1.BiformPointCoordinates PaperP1.BiformLinearCoordinates

def sourceForms (c₁ c₂ : ℤ) : Fin 3 → MvPolynomial (Fin 2) ℤ :=
  ![C c₂ * X 0, 0, C (-c₁) * X 1]

theorem source_homogeneous (c₁ c₂ : ℤ) : ∀ i, (sourceForms c₁ c₂ i).IsHomogeneous 1 := by
  intro i
  fin_cases i
  · exact MvPolynomial.isHomogeneous_C_mul_X _ _
  · exact MvPolynomial.isHomogeneous_zero (Fin 2) ℤ 1
  · exact MvPolynomial.isHomogeneous_C_mul_X _ _

theorem source_evaluation (c₁ c₂ : ℤ) (x y : Fin 2 → ℤ) :
    BidegreeOneElimination.original (sourceForms c₁ c₂) x y =
      c₂ * x 1 ^ 2 * y 0 - c₁ * x 0 ^ 2 * y 1 := by
  norm_num [sourceForms, BidegreeOneElimination.original, Fin.sum_univ_succ]
  ring

theorem inverse_equation_value {a b : ℕ} (A B C D : Matrix (Fin 2) (Fin 2) ℤ)
    (hAB : A * B = 1) (hCD : C * D = 1)
    (F : Fin (a + 1) → MvPolynomial (Fin 2) ℤ) (hF : ∀ i, (F i).IsHomogeneous b)
    (p : (Fin 2 → ℤ) × (Fin 2 → ℤ)) :
    BidegreeOneElimination.original (transform (b := b) A C F) (move B D p).1 (move B D p).2 =
      BidegreeOneElimination.original F p.1 p.2 := by
  rw [transform_evaluation A C F hF]
  change BidegreeOneElimination.original F (A.mulVec (B.mulVec p.1)) (C.mulVec (D.mulVec p.2)) = _
  rw [PaperP1.UnimodularBinaryCoordinates.reconstruct B A hAB, PaperP1.UnimodularBinaryCoordinates.reconstruct D C hCD]

end PaperP1.SourceBihomogeneousEquation
