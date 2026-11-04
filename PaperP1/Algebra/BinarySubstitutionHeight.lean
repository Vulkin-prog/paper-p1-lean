module

public import PaperP1.Algebra.BinaryLinearSubstitution
public import PaperP1.Algebra.PolynomialHeightArithmetic
public import PaperP1.Diophantine.BihomogeneousSwap

/-! # Explicit coefficient heights under integral binary coordinate changes -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BinarySubstitutionHeight

open Finset Polynomial PaperP1.BivariateDegrees PaperP1.PolynomialHeightArithmetic
open PaperP1.BinaryLinearSubstitution PaperP1.HomogeneousCharts

theorem linear_mul (a b : ℤ) (p : ℤ[X]) :
    integerPolynomialHeight ((C a * X + C b) * p) ≤
      (a.natAbs + b.natAbs) * integerPolynomialHeight p := by
  rw [add_mul, mul_assoc]
  exact (integer_height_add _ _).trans
    ((Nat.add_le_add ((integer_height_C_mul a (X * p)).trans
      (Nat.mul_le_mul_left _ (integer_height_X_mul p)))
      (integer_height_C_mul b p)).trans_eq (by ring))

theorem linear_pow (a b : ℤ) (n : ℕ) :
    integerPolynomialHeight ((C a * X + C b) ^ n) ≤ (a.natAbs + b.natAbs) ^ n := by
  induction n with
  | zero =>
    simp only [pow_zero]
    apply integer_height_le
    intro j
    simp only [Polynomial.coeff_one]
    split_ifs <;> norm_num
  | succ n ih =>
    rw [pow_succ']
    exact (linear_mul a b _).trans ((Nat.mul_le_mul_left _ ih).trans_eq (pow_succ' _ n).symm)

theorem product_linear_powers (a b c e : ℤ) (j k : ℕ) :
    integerPolynomialHeight ((C a * X + C b) ^ j * (C c * X + C e) ^ k) ≤
      (a.natAbs + b.natAbs) ^ j * (c.natAbs + e.natAbs) ^ k := by
  induction j with
  | zero => simpa only [pow_zero, one_mul] using linear_pow c e k
  | succ j ih =>
    rw [pow_succ', mul_assoc]
    exact (linear_mul a b _).trans ((Nat.mul_le_mul_left _ ih).trans_eq (by ring))

theorem chart_substitute (A : Matrix (Fin 2) (Fin 2) ℤ)
    (F : MvPolynomial (Fin 2) ℤ) (d : ℕ) (hF : F.IsHomogeneous d) :
    chart (substitute A F) = ∑ j : Fin (d + 1),
      C ((chart F).coeff j.val) * (C (A 0 0) * X + C (A 0 1)) ^ j.val *
        (C (A 1 0) * X + C (A 1 1)) ^ (d - j.val) := by
  conv_lhs => rw [PaperP1.BihomogeneousSwap.binary_expansion F hF]
  simp [chart, substitute, linearForm, Fin.sum_univ_two]

theorem chart_height (A : Matrix (Fin 2) (Fin 2) ℤ)
    (F : MvPolynomial (Fin 2) ℤ) (d H M : ℕ) (hF : F.IsHomogeneous d)
    (hH : ∀ m, (F.coeff m).natAbs ≤ H) (hM : ∀ i j, (A i j).natAbs ≤ M) :
    integerPolynomialHeight (chart (substitute A F)) ≤ (d + 1) * H * (2 * M) ^ d := by
  rw [chart_substitute A F d hF]
  calc
    _ ≤ ∑ j : Fin (d + 1), integerPolynomialHeight
        (C ((chart F).coeff j.val) * (C (A 0 0) * X + C (A 0 1)) ^ j.val *
          (C (A 1 0) * X + C (A 1 1)) ^ (d - j.val)) := integer_height_sum _ _
    _ ≤ ∑ _j : Fin (d + 1), H * (2 * M) ^ d := by
      apply sum_le_sum
      intro j _
      have hj : j.val ≤ d := by have := j.isLt; omega
      have hc : ((chart F).coeff j.val).natAbs ≤ H := by
        rw [chart_coeff F hF j.val hj]
        exact hH _
      rw [mul_assoc]
      calc
        _ ≤ ((chart F).coeff j.val).natAbs *
            integerPolynomialHeight ((C (A 0 0) * X + C (A 0 1)) ^ j.val *
              (C (A 1 0) * X + C (A 1 1)) ^ (d - j.val)) := integer_height_C_mul _ _
        _ ≤ H * ((A 0 0).natAbs + (A 0 1).natAbs) ^ j.val *
            ((A 1 0).natAbs + (A 1 1).natAbs) ^ (d - j.val) := by
          simpa only [mul_assoc] using Nat.mul_le_mul hc (product_linear_powers _ _ _ _ _ _)
        _ ≤ H * (2 * M) ^ j.val * (2 * M) ^ (d - j.val) := by
          gcongr
          · have := hM 0 0; have := hM 0 1; omega
          · have := hM 1 0; have := hM 1 1; omega
        _ = H * (2 * M) ^ d := by rw [mul_assoc, ← pow_add, Nat.add_sub_of_le hj]
    _ = _ := by simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]; ring

theorem coefficient_of_chart_height (F : MvPolynomial (Fin 2) ℤ) (d H : ℕ)
    (hF : F.IsHomogeneous d) (hH : integerPolynomialHeight (chart F) ≤ H) :
    ∀ m, (F.coeff m).natAbs ≤ H := by
  intro m
  have he := congrArg (fun G : MvPolynomial (Fin 2) ℤ ↦ G.coeff m) (chart_homogenize F hF)
  rw [Polynomial.coeff_homogenize] at he
  rw [← he]
  split_ifs
  · exact (coeff_natAbs_le_integerPolynomialHeight _ _).trans hH
  · simp

theorem coefficient_height (A : Matrix (Fin 2) (Fin 2) ℤ)
    (F : MvPolynomial (Fin 2) ℤ) (d H M : ℕ) (hF : F.IsHomogeneous d)
    (hH : ∀ m, (F.coeff m).natAbs ≤ H) (hM : ∀ i j, (A i j).natAbs ≤ M) :
    ∀ m, ((substitute A F).coeff m).natAbs ≤ (d + 1) * H * (2 * M) ^ d :=
  coefficient_of_chart_height _ d _ (substitute_homogeneous A F d hF) (chart_height A F d H M hF hH hM)

end PaperP1.BinarySubstitutionHeight
