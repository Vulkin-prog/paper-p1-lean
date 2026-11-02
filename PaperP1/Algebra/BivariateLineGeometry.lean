module

public import PaperP1.Algebra.BivariateTotalDegree
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! # Actual degree-one nested polynomials are lines and their points are collinear -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BivariateLineGeometry

open Polynomial PaperP1.BivariateTotalDegree

local instance : CommRing ℤ[X][X] := inferInstance

theorem exists_linear_form (P : ℤ[X][X]) (hD : totalDegree P = 1) :
    ∃ a b c : ℤ, (a ≠ 0 ∨ b ≠ 0) ∧ ∀ x y : ℤ, P.evalEval x y = a * x + b * y + c := by
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

theorem points_cross (P : ℤ[X][X]) (hD : totalDegree P = 1) (p q r : ℤ × ℤ)
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

end PaperP1.BivariateLineGeometry
