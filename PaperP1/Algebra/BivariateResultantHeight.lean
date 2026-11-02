module

public import PaperP1.Algebra.PolynomialDeterminantHeight
public import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-! # A coefficient-uniform height for the actual bivariate resultant -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BivariateResultantHeight

open Polynomial PaperP1.BivariateDegrees PaperP1.BivariateHeight PaperP1.PolynomialHeightArithmetic

theorem sylvester_entry_degree (f g : ℤ[X][X]) (m n d : ℕ)
    (hf : degreeX f ≤ d) (hg : degreeX g ≤ d) (i j : Fin (m + n)) :
    (Polynomial.sylvester f g m n i j).natDegree ≤ d := by
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j
  · simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left]
    split_ifs
    · exact (natDegree_coeff_le_degreeX g _).trans hg
    · simp
  · simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right]
    split_ifs
    · exact (natDegree_coeff_le_degreeX f _).trans hf
    · simp

theorem sylvester_entry_height (f g : ℤ[X][X]) (m n H : ℕ)
    (hf : height f ≤ H) (hg : height g ≤ H) (i j : Fin (m + n)) :
    PaperP1.integerPolynomialHeight (Polynomial.sylvester f g m n i j) ≤ H := by
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j
  · simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left]
    split_ifs
    · exact (row_height_le g _).trans hg
    · simp [PaperP1.integerPolynomialHeight]
  · simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right]
    split_ifs
    · exact (row_height_le f _).trans hf
    · simp [PaperP1.integerPolynomialHeight]

theorem resultant_height (f g : ℤ[X][X]) (m n d H : ℕ)
    (hfd : degreeX f ≤ d) (hgd : degreeX g ≤ d) (hfH : height f ≤ H) (hgH : height g ≤ H) :
    PaperP1.integerPolynomialHeight (f.resultant g m n) ≤
      (m + n).factorial * ((((m + n) * d + 1) * H) ^ (m + n)) := by
  simpa only [Polynomial.resultant, Fintype.card_fin] using
    PolynomialDeterminantHeight.determinant_height (Polynomial.sylvester f g m n) d H
      (sylvester_entry_degree f g m n d hfd hgd) (sylvester_entry_height f g m n H hfH hgH)

end PaperP1.BivariateResultantHeight
