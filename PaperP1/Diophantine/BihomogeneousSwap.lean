module

public import PaperP1.Diophantine.HomogeneousCharts
public import PaperP1.Diophantine.BidegreeOneElimination

/-! # Exact exchange of the two primitive pairs in a bihomogeneous equation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BihomogeneousSwap

open Finset Polynomial MvPolynomial PaperP1.HomogeneousCharts

variable {R : Type*} [CommRing R]

theorem binary_expansion (F : MvPolynomial (Fin 2) R) {d : ℕ} (hF : F.IsHomogeneous d) :
    F = ∑ j : Fin (d + 1), MvPolynomial.C ((chart F).coeff j.val) *
      MvPolynomial.X 0 ^ j.val * MvPolynomial.X 1 ^ (d - j.val) := by
  have hp : chart F = ∑ j : Fin (d + 1), Polynomial.C ((chart F).coeff j.val) * Polynomial.X ^ j.val := by
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ ↦ Polynomial.C ((chart F).coeff j) * Polynomial.X ^ j)]
    exact (chart F).as_sum_range_C_mul_X_pow' (Nat.lt_succ_of_le (chart_degree F hF))
  calc
    F = (chart F).homogenize d := (chart_homogenize F hF).symm
    _ = (∑ j : Fin (d + 1), Polynomial.C ((chart F).coeff j.val) * Polynomial.X ^ j.val).homogenize d := congrArg (fun p : R[X] ↦ p.homogenize d) hp
    _ = _ := by
      rw [Polynomial.homogenize_finsetSum]
      apply sum_congr rfl
      intro j _
      rw [Polynomial.homogenize_C_mul, Polynomial.homogenize_X_pow (show j.val ≤ d by have := j.isLt; omega)]
      ring

theorem eval_binary_expansion (F : MvPolynomial (Fin 2) R) {d : ℕ} (hF : F.IsHomogeneous d)
    (z : Fin 2 → R) :
    eval z F = ∑ j : Fin (d + 1), (chart F).coeff j.val * z 0 ^ j.val * z 1 ^ (d - j.val) := by
  conv_lhs => rw [binary_expansion F hF]
  simp only [MvPolynomial.eval_sum, map_mul, MvPolynomial.eval_C, map_pow, MvPolynomial.eval_X]

def coefficients {ell k : ℕ} (C : Fin (ell + 1) → MvPolynomial (Fin 2) R)
    (j : Fin (k + 1)) : MvPolynomial (Fin 2) R :=
  ∑ i, MvPolynomial.C ((chart (C i)).coeff j.val) * MvPolynomial.X 0 ^ i.val *
    MvPolynomial.X 1 ^ (ell - i.val)

theorem coefficients_homogeneous {ell k : ℕ}
    (C : Fin (ell + 1) → MvPolynomial (Fin 2) R) (j : Fin (k + 1)) :
    (coefficients C j).IsHomogeneous ell := by
  apply IsHomogeneous.sum
  intro i _
  have hi : i.val ≤ ell := by have := i.isLt; omega
  have h := ((isHomogeneous_C (Fin 2) ((chart (C i)).coeff j.val)).mul ((isHomogeneous_X (R := R) 0).pow i.val)).mul
    ((isHomogeneous_X (R := R) 1).pow (ell - i.val))
  simpa only [one_mul, zero_add, Nat.add_sub_of_le hi] using h

theorem eval_coefficients {ell k : ℕ}
    (C : Fin (ell + 1) → MvPolynomial (Fin 2) R) (j : Fin (k + 1)) (v : Fin 2 → R) :
    eval v (coefficients C j) =
      ∑ i, (chart (C i)).coeff j.val * v 0 ^ i.val * v 1 ^ (ell - i.val) := by
  simp only [coefficients, MvPolynomial.eval_sum, map_mul, MvPolynomial.eval_C, map_pow, MvPolynomial.eval_X]

theorem original_swap {ell k : ℕ} (C : Fin (ell + 1) → MvPolynomial (Fin 2) ℤ)
    (hC : ∀ i, (C i).IsHomogeneous k) (v z : Fin 2 → ℤ) :
    PaperP1.BidegreeOneElimination.original (coefficients (k := k) C) z v =
      PaperP1.BidegreeOneElimination.original C v z := by
  unfold PaperP1.BidegreeOneElimination.original
  simp_rw [eval_coefficients, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro i _
  rw [eval_binary_expansion (C i) (hC i)]
  simp_rw [Finset.sum_mul]
  apply sum_congr rfl
  intro j _
  ring

end PaperP1.BihomogeneousSwap
