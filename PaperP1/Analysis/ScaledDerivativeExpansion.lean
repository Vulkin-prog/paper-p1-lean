module

public import PaperP1.Analysis.IteratedDerivativeMonotonicity
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Tactic.Ring

/-! # Actual derivative expansions for a smoothly scaled differential chain

If F_k'=a F_(k+1), the actual n-th derivative of F_0 has a finite lower
triangular expansion. Its leading coefficient is a^n.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ScaledDerivativeExpansion

open Set Finset
open scoped ContDiff

def coefficient (a : ℝ → ℝ) : ℕ → ℕ → ℝ → ℝ
  | 0, k => fun _ ↦ if k = 0 then 1 else 0
  | n + 1, k => fun t ↦ deriv (coefficient a n k) t +
      if k = 0 then 0 else a t * coefficient a n (k - 1) t

theorem coefficient_above (a : ℝ → ℝ) (n k : ℕ) (hnk : n < k) :
    coefficient a n k = fun _ ↦ 0 := by
  induction n generalizing k with
  | zero =>
    have hk : k ≠ 0 := by omega
    funext t
    simp only [coefficient, hk, ite_false]
  | succ n ih =>
    have hk : k ≠ 0 := by omega
    have h₁ := ih k (by omega)
    have h₂ := ih (k - 1) (by omega)
    funext t
    simp only [coefficient, h₁, h₂, deriv_const, hk, ite_false, mul_zero, add_zero]

theorem coefficient_diagonal (a : ℝ → ℝ) (n : ℕ) (t : ℝ) :
    coefficient a n n t = (a t) ^ n := by
  induction n with
  | zero => simp only [coefficient, ite_true, pow_zero]
  | succ n ih =>
    have hz := coefficient_above a n (n + 1) (by omega)
    simp only [coefficient, hz, deriv_const, show n + 1 ≠ 0 by omega, ite_false,
      Nat.add_sub_cancel, zero_add, ih, pow_succ]
    ring

theorem smooth_coefficient (a : ℝ → ℝ) (s : Set ℝ) (hs : IsOpen s)
    (ha : ContDiffOn ℝ ∞ a s) (n k : ℕ) : ContDiffOn ℝ ∞ (coefficient a n k) s := by
  induction n generalizing k with
  | zero => exact contDiffOn_const
  | succ n ih =>
    have hD : ContDiffOn ℝ ∞ (deriv (coefficient a n k)) s :=
      (ih k).deriv_of_isOpen hs (by simp)
    by_cases hk : k = 0
    · simp only [coefficient, hk, ite_true, add_zero]
      exact (ih 0).deriv_of_isOpen hs (by simp)
    · simp only [coefficient, hk, ite_false]
      exact hD.add (ha.mul (ih (k - 1)))

theorem successor_sum (a : ℝ → ℝ) (F : ℕ → ℝ → ℝ) (n : ℕ) (t : ℝ) :
    (∑ k ∈ range (n + 2), coefficient a (n + 1) k t * F k t) =
      ∑ k ∈ range (n + 1),
        (deriv (coefficient a n k) t * F k t + coefficient a n k t * (a t * F (k + 1) t)) := by
  have hz := coefficient_above a n (n + 1) (by omega)
  have hD : (∑ k ∈ range (n + 2), deriv (coefficient a n k) t * F k t) =
      ∑ k ∈ range (n + 1), deriv (coefficient a n k) t * F k t := by
    rw [show n + 2 = (n + 1) + 1 by omega, sum_range_succ, hz]
    simp only [deriv_const, zero_mul, add_zero]
  have hS : (∑ k ∈ range (n + 2),
      (if k = 0 then 0 else a t * coefficient a n (k - 1) t) * F k t) =
        ∑ k ∈ range (n + 1), coefficient a n k t * (a t * F (k + 1) t) := by
    rw [show n + 2 = (n + 1) + 1 by omega, sum_range_succ']
    simp only [show ∀ k : ℕ, k + 1 ≠ 0 by intro k; omega, ite_false, ite_true,
      Nat.add_sub_cancel, zero_mul, add_zero]
    apply sum_congr rfl
    intro k _hk
    ring
  calc
    _ = ∑ k ∈ range (n + 2), (deriv (coefficient a n k) t * F k t +
        (if k = 0 then 0 else a t * coefficient a n (k - 1) t) * F k t) := by
      apply sum_congr rfl
      intro k _hk
      rw [coefficient, add_mul]
    _ = (∑ k ∈ range (n + 2), deriv (coefficient a n k) t * F k t) +
        ∑ k ∈ range (n + 2), (if k = 0 then 0 else a t * coefficient a n (k - 1) t) * F k t :=
      sum_add_distrib
    _ = _ := by rw [hD, hS, ← sum_add_distrib]

theorem iterated_expansion (a : ℝ → ℝ) (F : ℕ → ℝ → ℝ) (s : Set ℝ) (hs : IsOpen s)
    (ha : ContDiffOn ℝ ∞ a s)
    (hF : ∀ k, ∀ t ∈ s, HasDerivAt (F k) (a t * F (k + 1) t) t) (n : ℕ) :
    EqOn (iteratedDeriv n (F 0))
      (fun t ↦ ∑ k ∈ range (n + 1), coefficient a n k t * F k t) s := by
  induction n with
  | zero =>
    intro t _ht
    simp only [Nat.zero_add, iteratedDeriv_zero, sum_range_one, coefficient, ite_true, one_mul]
  | succ n ih =>
    intro t ht
    have hC (k : ℕ) : HasDerivAt (coefficient a n k) (deriv (coefficient a n k) t) t :=
      (((smooth_coefficient a s hs ha n k).differentiableOn (by simp) t ht).differentiableAt
        (hs.mem_nhds ht)).hasDerivAt
    have hG : HasDerivAt (fun u ↦ ∑ k ∈ range (n + 1), coefficient a n k u * F k u)
        (∑ k ∈ range (n + 1), (deriv (coefficient a n k) t * F k t +
          coefficient a n k t * (a t * F (k + 1) t))) t :=
      HasDerivAt.fun_sum (fun k _hk ↦ HasDerivAt.fun_mul (hC k) (hF k t ht))
    rw [iteratedDeriv_succ]
    calc
      _ = deriv (fun u ↦ ∑ k ∈ range (n + 1), coefficient a n k u * F k u) t := (ih.deriv hs) ht
      _ = _ := hG.deriv
      _ = _ := (successor_sum a F n t).symm

end PaperP1.ScaledDerivativeExpansion
