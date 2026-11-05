module

public import PaperP1.Algebra.PolynomialGradientDegree
public import PaperP1.Algebra.MvPlaneBezout

/-! # A polynomial barrier for singular and box-boundary ends of curve components -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CurveComponentBarrier

open MvPolynomial

def barrier (P : MvPolynomial (Fin 2) ℝ) : MvPolynomial (Fin 2) ℝ :=
  ((pderiv 0 P) ^ 2 + (pderiv 1 P) ^ 2) * (1 - X 0 ^ 2) * (1 - X 1 ^ 2)

def level (P : MvPolynomial (Fin 2) ℝ) (ε : ℝ) : MvPolynomial (Fin 2) ℝ :=
  barrier P - C ε

theorem evaluation (P : MvPolynomial (Fin 2) ℝ) (z : Fin 2 → ℝ) :
    eval z (barrier P) =
      ((eval z (pderiv 0 P)) ^ 2 + (eval z (pderiv 1 P)) ^ 2) *
        (1 - z 0 ^ 2) * (1 - z 1 ^ 2) := by
  simp [barrier]

theorem degree (P : MvPolynomial (Fin 2) ℝ) :
    (barrier P).totalDegree ≤ 2 * P.totalDegree + 4 := by
  have hd (i : Fin 2) : (pderiv i P).totalDegree ≤ P.totalDegree :=
    (PolynomialGradientDegree.pderiv_degree_le_sub_one P i).trans (Nat.sub_le _ _)
  have hsq (i : Fin 2) : ((pderiv i P) ^ 2).totalDegree ≤ 2 * P.totalDegree :=
    (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (hd i))
  have hsum : ((pderiv 0 P) ^ 2 + (pderiv 1 P) ^ 2).totalDegree ≤ 2 * P.totalDegree :=
    (totalDegree_add _ _).trans (max_le (hsq 0) (hsq 1))
  have hbox (i : Fin 2) : (1 - (X i : MvPolynomial (Fin 2) ℝ) ^ 2).totalDegree ≤ 2 := by
    apply (totalDegree_sub _ _).trans
    simp only [totalDegree_one, totalDegree_X_pow, Nat.max_eq_right (by omega : 0 ≤ 2)]
    rfl
  have hmul := totalDegree_mul
    (((pderiv 0 P) ^ 2 + (pderiv 1 P) ^ 2) * (1 - X 0 ^ 2)) (1 - X 1 ^ 2)
  have hmul' := totalDegree_mul ((pderiv 0 P) ^ 2 + (pderiv 1 P) ^ 2) (1 - X 0 ^ 2)
  change (((pderiv 0 P) ^ 2 + (pderiv 1 P) ^ 2) * (1 - X 0 ^ 2) *
    (1 - X 1 ^ 2)).totalDegree ≤ _
  have hbox0 := hbox 0
  have hbox1 := hbox 1
  omega

theorem level_degree (P : MvPolynomial (Fin 2) ℝ) (ε : ℝ) :
    (level P ε).totalDegree ≤ 2 * P.totalDegree + 4 :=
  (totalDegree_sub_C_le _ _).trans (degree P)

theorem positive (P : MvPolynomial (Fin 2) ℝ) (z : Fin 2 → ℝ)
    (hbox : ∀ i, |z i| < 1) (hgrad : ∃ i, eval z (pderiv i P) ≠ 0) :
    0 < eval z (barrier P) := by
  rw [evaluation]
  have hsum : 0 < (eval z (pderiv 0 P)) ^ 2 + (eval z (pderiv 1 P)) ^ 2 := by
    obtain ⟨i, hi⟩ := hgrad
    fin_cases i
    · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hi) (sq_nonneg _)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hi)
  exact mul_pos (mul_pos hsum (sub_pos.mpr ((sq_lt_one_iff_abs_lt_one _).mpr (hbox 0))))
    (sub_pos.mpr ((sq_lt_one_iff_abs_lt_one _).mpr (hbox 1)))

theorem zero_of_gradient (P : MvPolynomial (Fin 2) ℝ) (z : Fin 2 → ℝ)
    (hgrad : ∀ i, eval z (pderiv i P) = 0) : eval z (barrier P) = 0 := by
  simp [evaluation, hgrad]

theorem zero_of_boundary (P : MvPolynomial (Fin 2) ℝ) (z : Fin 2 → ℝ)
    (hboundary : ∃ i, |z i| = 1) : eval z (barrier P) = 0 := by
  obtain ⟨i, hi⟩ := hboundary
  have hs : z i ^ 2 = 1 := by rw [← sq_abs (z i), hi, one_pow]
  fin_cases i
  · change z 0 ^ 2 = 1 at hs
    simp only [evaluation, hs, sub_self, mul_zero, zero_mul]
  · change z 1 ^ 2 = 1 at hs
    simp only [evaluation, hs, sub_self, mul_zero]

theorem level_not_dvd (P : MvPolynomial (Fin 2) ℝ) (w : Fin 2 → ℝ) (ε : ℝ)
    (hP : eval w P = 0) (hw : eval w (barrier P) = 0) (hε : ε ≠ 0) :
    ¬P ∣ level P ε := by
  rintro ⟨A, hA⟩
  have he := congrArg (eval w) hA
  simp only [level, map_sub, eval_C, map_mul, hP, hw, zero_mul, zero_sub] at he
  exact hε (neg_eq_zero.mp he)

theorem level_population_card (P : MvPolynomial (Fin 2) ℝ) (hP : Irreducible P)
    (w : Fin 2 → ℝ) (hwP : eval w P = 0) (hw : eval w (barrier P) = 0)
    (ε : ℝ) (hε : ε ≠ 0) (S : Finset (Fin 2 → ℝ))
    (hS : ∀ z ∈ S, eval z P = 0 ∧ eval z (barrier P) = ε) :
    S.card ≤ P.totalDegree * (2 * P.totalDegree + 4) := by
  have hc := MvPlaneBezout.common_points_card P (level P ε) hP
    (level_not_dvd P w ε hwP hw hε) S (by
      intro z hz
      obtain ⟨hzP, hzH⟩ := hS z hz
      exact ⟨hzP, by simp [level, hzH]⟩)
  exact hc.trans (Nat.mul_le_mul_left _ (level_degree P ε))

end PaperP1.CurveComponentBarrier
