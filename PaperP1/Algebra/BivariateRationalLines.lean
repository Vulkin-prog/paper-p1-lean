module

public import PaperP1.Algebra.BivariateFactorDegree
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! # Actual rational degree-one polynomials and collinear integer points -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BivariateRationalLines

open Polynomial PaperP1.BivariateFactorDegree

theorem totalDegree_zero : totalDegree (0 : ℚ[X][X]) = 0 := by simp [totalDegree]

theorem exists_coefficient_degree (P : ℚ[X][X]) (hP : P ≠ 0) :
    ∃ i j : ℕ, (P.coeff j).coeff i ≠ 0 ∧ i + j = totalDegree P := by
  obtain ⟨j, hj, he⟩ := Finset.exists_mem_eq_sup P.support (support_nonempty.mpr hP)
    (fun j ↦ j + (P.coeff j).natDegree)
  have hrow : P.coeff j ≠ 0 := mem_support_iff.mp hj
  refine ⟨(P.coeff j).natDegree, j, ?_, ?_⟩
  · simpa only [coeff_natDegree] using leadingCoeff_ne_zero.mpr hrow
  · unfold totalDegree
    rw [he, add_comm]

theorem exists_linear_form (P : ℚ[X][X]) (hD : totalDegree P = 1) :
    ∃ a b c : ℚ, (a ≠ 0 ∨ b ≠ 0) ∧ ∀ x y : ℚ, P.evalEval x y = a * x + b * y + c := by
  let a := (P.coeff 0).coeff 1
  let b := (P.coeff 1).coeff 0
  let c := (P.coeff 0).coeff 0
  have hzero (m n : ℕ) (h : 1 < m + n) : (P.coeff n).coeff m = 0 := by
    by_contra hn
    have hc := coefficient_degree_le P m n hn
    omega
  have hrow₀ : P.coeff 0 = C c + monomial 1 a := by
    apply Polynomial.ext
    intro m
    rw [coeff_add, coeff_C, coeff_monomial]
    by_cases hm₀ : m = 0
    · subst m
      norm_num
      rfl
    · by_cases hm₁ : m = 1
      · subst m
        norm_num
        rfl
      · rw [ite_eq_right hm₀, ite_eq_right (Ne.symm hm₁), zero_add]
        exact hzero m 0 (by omega)
  have hrow₁ : P.coeff 1 = C b := by
    apply Polynomial.ext
    intro m
    rw [coeff_C]
    by_cases hm₀ : m = 0
    · subst m
      simp only [ite_true]
      rfl
    · rw [ite_eq_right hm₀]
      exact hzero m 1 (by omega)
  have hrow (n : ℕ) (hn₀ : n ≠ 0) (hn₁ : n ≠ 1) : P.coeff n = 0 := by
    apply Polynomial.ext
    intro m
    rw [coeff_zero]
    exact hzero m n (by omega)
  have hnormal : P = C (C c + monomial 1 a) + monomial 1 (C b) := by
    apply Polynomial.ext
    intro n
    rw [coeff_add, coeff_C, coeff_monomial]
    by_cases hn₀ : n = 0
    · subst n
      norm_num
      exact hrow₀
    · by_cases hn₁ : n = 1
      · subst n
        norm_num
        exact hrow₁
      · rw [ite_eq_right hn₀, ite_eq_right (Ne.symm hn₁), zero_add]
        exact hrow n hn₀ hn₁
  have hP : P ≠ 0 := by intro h; rw [h, totalDegree_zero] at hD; omega
  obtain ⟨m, n, hcoeff, hmn⟩ := exists_coefficient_degree P hP
  have hcases : (m = 1 ∧ n = 0) ∨ (m = 0 ∧ n = 1) := by omega
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl hcoeff
    · exact Or.inr hcoeff
  refine ⟨a, b, c, hab, ?_⟩
  intro x y
  rw [hnormal]
  simp [evalEval, eval_add, eval_monomial]
  ring

theorem points_cross (P : ℚ[X][X]) (hD : totalDegree P = 1) (p q r : ℚ × ℚ)
    (hp : P.evalEval p.1 p.2 = 0) (hq : P.evalEval q.1 q.2 = 0) (hr : P.evalEval r.1 r.2 = 0) :
    (q.1 - p.1) * (r.2 - p.2) = (q.2 - p.2) * (r.1 - p.1) := by
  obtain ⟨a, b, c, hab, heval⟩ := exists_linear_form P hD
  rw [heval] at hp hq hr
  have hq' : a * (q.1 - p.1) + b * (q.2 - p.2) = 0 := by linarith
  have hr' : a * (r.1 - p.1) + b * (r.2 - p.2) = 0 := by linarith
  apply sub_eq_zero.mp
  rcases hab with ha | hb
  · apply (mul_eq_zero.mp (show a * ((q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1)) = 0 from ?_)).resolve_left ha
    calc
      a * ((q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1)) =
          (a * (q.1 - p.1) + b * (q.2 - p.2)) * (r.2 - p.2) -
            (a * (r.1 - p.1) + b * (r.2 - p.2)) * (q.2 - p.2) := by ring
      _ = 0 := by rw [hq', hr']; ring
  · apply (mul_eq_zero.mp (show b * ((q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1)) = 0 from ?_)).resolve_left hb
    calc
      b * ((q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1)) =
          (a * (r.1 - p.1) + b * (r.2 - p.2)) * (q.1 - p.1) -
            (a * (q.1 - p.1) + b * (q.2 - p.2)) * (r.1 - p.1) := by ring
      _ = 0 := by rw [hq', hr']; ring

theorem integer_points_cross (P : ℚ[X][X]) (hD : totalDegree P = 1) (p q r : ℤ × ℤ)
    (hp : P.evalEval (p.1 : ℚ) (p.2 : ℚ) = 0)
    (hq : P.evalEval (q.1 : ℚ) (q.2 : ℚ) = 0)
    (hr : P.evalEval (r.1 : ℚ) (r.2 : ℚ) = 0) :
    (q.1 - p.1) * (r.2 - p.2) = (q.2 - p.2) * (r.1 - p.1) := by
  have he := points_cross P hD ((p.1 : ℚ), (p.2 : ℚ))
    ((q.1 : ℚ), (q.2 : ℚ)) ((r.1 : ℚ), (r.2 : ℚ)) hp hq hr
  dsimp only at he
  exact_mod_cast he

end PaperP1.BivariateRationalLines
