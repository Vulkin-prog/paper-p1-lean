module

public import PaperP1.Algebra.P3GraphPlaneCone
public import PaperP1.Diophantine.GraphPlanePointCounts

/-! # Exact affine point count for a literal cone in the omitted graph-plane coordinate -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3ConePlanePointCount

open MvPolynomial GraphPlanePointCounts
open scoped Classical

theorem cardinality {F : Type} [Field F] [Fintype F] (Q : MvPolynomial (Fin 3) F) :
    (affineZeros (rename Fin.succ Q)).card = Fintype.card F * (affineZeros Q).card := by
  have hm := first_moment (rename Fin.succ Q)
  simp_rw [P3GraphPlaneCone.section_rename] at hm
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    smul_eq_mul] at hm
  have he : (affineZeros (rename Fin.succ Q)).card * Fintype.card F ^ 2 =
      (Fintype.card F * (affineZeros Q).card) * Fintype.card F ^ 2 := by
    rw [← hm]
    ring
  exact (mul_right_cancel₀ (pow_ne_zero 2 (Nat.ne_of_gt Fintype.card_pos))) he

theorem upper_bound {F : Type} [Field F] [Fintype F] (Q : MvPolynomial (Fin 3) F)
    (B : ℝ) (hB : ((affineZeros Q).card : ℝ) ≤ B) :
    ((affineZeros (rename Fin.succ Q)).card : ℝ) ≤ (Fintype.card F : ℝ) * B := by
  rw [cardinality, Nat.cast_mul]
  exact mul_le_mul_of_nonneg_left hB (by positivity)

end PaperP1.P3ConePlanePointCount
