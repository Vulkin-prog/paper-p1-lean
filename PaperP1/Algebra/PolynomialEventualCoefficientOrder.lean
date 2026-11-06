module

public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Tactic.Linarith

/-! # Eventual inequalities of actual polynomial evaluations control their top coefficients -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PolynomialEventualCoefficientOrder

open Polynomial Filter

theorem coefficient_le (p q : ℚ[X]) (r : ℕ) (hp : p.natDegree ≤ r) (hq : q.natDegree ≤ r)
    (N : ℕ) (h : ∀ n : ℕ, N ≤ n → p.eval (n : ℚ) ≤ q.eval (n : ℚ)) :
    p.coeff r ≤ q.coeff r := by
  by_contra hbad
  have hc : 0 < (p - q).coeff r := by rw [coeff_sub]; exact sub_pos.mpr (lt_of_not_ge hbad)
  have hd : (p - q).natDegree = r :=
    natDegree_eq_of_le_of_coeff_ne_zero ((natDegree_sub_le p q).trans (max_le hp hq)) hc.ne'
  have hl : 0 < (p - q).leadingCoeff := by rw [Polynomial.leadingCoeff, hd]; exact hc
  by_cases hr : r = 0
  · have he : p - q = C ((p - q).coeff 0) := eq_C_of_natDegree_eq_zero (hd.trans hr)
    have hn := h N le_rfl
    have ht : 0 < (p - q).eval (N : ℚ) := by rw [he, eval_C]; simpa only [hr] using hc
    rw [eval_sub] at ht
    linarith
  · have hdegree : 0 < (p - q).degree := natDegree_pos_iff_degree_pos.mp (by omega)
    have ht := ((p - q).tendsto_atTop_of_leadingCoeff_nonneg hdegree hl.le).comp
      (tendsto_natCast_atTop_atTop (R := ℚ))
    have he : ∀ᶠ n : ℕ in atTop, (p - q).eval (n : ℚ) ≤ 0 := by
      exact eventually_atTop.mpr ⟨N, fun n hn ↦ by rw [eval_sub]; exact sub_nonpos.mpr (h n hn)⟩
    obtain ⟨n, hle, hgt⟩ := (he.and (ht.eventually_gt_atTop 0)).exists
    exact (not_lt_of_ge hle) hgt

theorem translation_degree_le (p : ℚ[X]) (t : ℚ) (r : ℕ) (hp : p.natDegree ≤ r) :
    (p.comp (X + C t)).natDegree ≤ r := by
  simpa only [natDegree_comp, natDegree_X_add_C, mul_one] using hp

theorem translation_coefficient (p : ℚ[X]) (t : ℚ) (r : ℕ) (hp : p.natDegree ≤ r) :
    (p.comp (X + C t)).coeff r = p.coeff r := by
  by_cases he : p.natDegree = r
  · calc
      (p.comp (X + C t)).coeff r = (p.comp (X + C t)).leadingCoeff := by
        rw [Polynomial.leadingCoeff, natDegree_comp, natDegree_X_add_C, mul_one, he]
      _ = p.leadingCoeff := by rw [leadingCoeff_comp (by simp)]; simp
      _ = p.coeff r := by rw [Polynomial.leadingCoeff, he]
  · have hlt : p.natDegree < r := lt_of_le_of_ne hp he
    rw [coeff_eq_zero_of_natDegree_lt hlt, coeff_eq_zero_of_natDegree_lt]
    simpa only [natDegree_comp, natDegree_X_add_C, mul_one] using hlt

end PaperP1.PolynomialEventualCoefficientOrder
