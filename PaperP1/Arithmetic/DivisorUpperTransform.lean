module

public import Mathlib.NumberTheory.SelbergSieve

/-! # Exact inversion of the actual upper-divisor transform -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DivisorUpperTransform
open Finset Nat ArithmeticFunction
open scoped Classical ArithmeticFunction.Moebius

theorem quotient_sum (P : ℕ) (f : ℕ → ℝ) :
    (∑ d ∈ P.divisors, f (P/d))=∑ d ∈ P.divisors, f d := by
  exact (Nat.sum_divisorsAntidiagonal (fun _ b ↦ f b) (n := P)).symm.trans
    (Nat.sum_divisorsAntidiagonal' (fun _ b ↦ f b) (n := P))

theorem multiples_complement_sum (P l : ℕ) (hP : P ≠ 0) (hl : l ∣ P) (f : ℕ → ℝ) :
    (∑ d ∈ P.divisors, if l ∣ d then f (P/d) else 0)=∑ d ∈ (P/l).divisors, f d := by
  have hq := quotient_sum P (fun d ↦ if l ∣ d then f (P/d) else 0)
  calc
    _ = ∑ e ∈ P.divisors, if l ∣ P/e then f (P/(P/e)) else 0 := hq.symm
    _ = ∑ e ∈ P.divisors, if e ∣ P/l then f e else 0 := by
      apply sum_congr rfl
      intro e he
      have hd := Nat.dvd_of_mem_divisors he
      have hi : l ∣ P/e ↔ e ∣ P/l := by
        rw [Nat.dvd_div_iff_mul_dvd hd,Nat.dvd_div_iff_mul_dvd hl,Nat.mul_comm l e]
      simp only [hi,Nat.div_div_self hd hP]
    _ = ∑ e ∈ P.divisors.filter (fun e ↦ e ∣ P/l), f e := by rw [sum_filter]
    _ = _ := by rw [Nat.divisors_filter_dvd_of_dvd hP (Nat.div_dvd_of_dvd hl)]

theorem multiples_quotient_sum (P l : ℕ) (hP : P ≠ 0) (hl : l ∣ P) (f : ℕ → ℝ) :
    (∑ d ∈ P.divisors, if l ∣ d then f d else 0)=∑ d ∈ (P/l).divisors, f (P/d) := by
  have hh := multiples_complement_sum P l hP hl (fun d ↦ f (P/d))
  have he : (∑ d ∈ P.divisors, if l ∣ d then f (P/(P/d)) else 0)=
      ∑ d ∈ P.divisors, if l ∣ d then f d else 0 := by
    apply sum_congr rfl
    intro d hd
    rw [Nat.div_div_self (Nat.dvd_of_mem_divisors hd) hP]
  rw [he] at hh
  exact hh

def lowerInverse (g : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ x ∈ n.divisorsAntidiagonal, (μ x.1 : ℝ)*g x.2

theorem lower_inverse_sum (g : ℕ → ℝ) (n : ℕ) (hn : 0 < n) :
    (∑ d ∈ n.divisors, lowerInverse g d)=g n := by
  have hh : ∀ n > 0, (∑ d ∈ n.divisors, lowerInverse g d)=g n :=
    (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq).mpr (fun n hn ↦ rfl)
  exact hh n hn

def upperInverse (P : ℕ) (c : ℕ → ℝ) (d : ℕ) : ℝ := lowerInverse (fun n ↦ c (P/n)) (P/d)

theorem upper_inverse_sum (P : ℕ) (c : ℕ → ℝ) (l : ℕ) (hP : P ≠ 0) (hl : l ∣ P) :
    (∑ d ∈ P.divisors, if l ∣ d then upperInverse P c d else 0)=c l := by
  have hq := multiples_complement_sum P l hP hl (lowerInverse (fun n ↦ c (P/n)))
  change (∑ d ∈ P.divisors, if l ∣ d then upperInverse P c d else 0)=_ at hq
  rw [hq,lower_inverse_sum _ _ (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hP) hl)
    (Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hP hl))),Nat.div_div_self hl hP]

theorem upper_inverse_explicit (P : ℕ) (c : ℕ → ℝ) (l : ℕ) (hP : P ≠ 0) (hl : l ∣ P) :
    upperInverse P c l=∑ d ∈ P.divisors, if l ∣ d then (μ (d/l) : ℝ)*c d else 0 := by
  have ha := Nat.sum_divisorsAntidiagonal' (fun a b ↦ (μ a : ℝ)*c (P/b)) (n := P/l)
  rw [upperInverse,lowerInverse,ha]
  rw [multiples_quotient_sum P l hP hl (fun d ↦ (μ (d/l) : ℝ)*c d)]
  apply sum_congr rfl
  intro d hd
  have he : (P/l)/d=(P/d)/l := by rw [Nat.div_div_eq_div_mul,Nat.div_div_eq_div_mul,Nat.mul_comm l d]
  rw [he]

theorem upper_inverse_one (P : ℕ) (c : ℕ → ℝ) (hP : P ≠ 0) :
    upperInverse P c 1=∑ d ∈ P.divisors, (μ d : ℝ)*c d := by
  rw [upper_inverse_explicit P c 1 hP (one_dvd P)]
  simp only [one_dvd,ite_true,Nat.div_one]
end DivisorUpperTransform
