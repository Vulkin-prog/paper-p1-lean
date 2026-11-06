module

public import PaperP1.Asymptotics.SlowPrimeBandSieve

/-! # The full weighted Ramare identity with a bounded actual residual coefficient -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RamareWeights
open Finset PaperP1 PrimeDivisorWeights
open scoped Classical

def weight (P : Finset ℕ) (n : ℕ) : ℝ :=
  ∑ p ∈ factors P n, 1/((count P (n/p)+1 : ℕ) : ℝ)

theorem weight_nonneg (P : Finset ℕ) (n : ℕ) : 0 ≤ weight P n := by
  exact sum_nonneg (fun p hp ↦ by positivity)

theorem quotient_count_ge (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime) (n p : ℕ)
    (hp : p ∈ factors P n) : count P n ≤ count P (n/p)+1 := by
  have hh := count_mul_prime P hP p (n/p) (mem_filter.mp hp).1
  rw [Nat.mul_div_cancel' (mem_filter.mp hp).2] at hh
  split_ifs at hh <;> omega

theorem weight_le_one (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n : ℕ) : weight P n ≤ 1 := by
  by_cases hz : count P n=0
  · have he : factors P n=∅ := card_eq_zero.mp hz
    simp [weight,he]
  · have hpos : 0 < count P n := by omega
    have hr : (0 : ℝ) < count P n := by exact_mod_cast hpos
    have hterm : ∀ p ∈ factors P n, 1/((count P (n/p)+1 : ℕ) : ℝ) ≤ 1/(count P n : ℝ) := by
      intro p hp
      exact div_le_div_of_nonneg_left (by norm_num) hr (by exact_mod_cast quotient_count_ge P hP n p hp)
    calc
      _ ≤ ∑ _p ∈ factors P n, 1/(count P n : ℝ) := sum_le_sum hterm
      _ = 1 := by simp only [sum_const,nsmul_eq_mul]; change (count P n : ℝ)*(1/count P n)=1; field_simp

theorem weight_eq_one (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n : ℕ)
    (hcount : 0 < count P n) (hsq : ∀ p ∈ P, ¬p^2 ∣ n) : weight P n=1 := by
  have he : weight P n = ∑ _p ∈ factors P n, 1/(count P n : ℝ) := by
    apply sum_congr rfl
    intro p hp
    rw [quotient_count_add_one P hP n p (mem_filter.mp hp).1 (mem_filter.mp hp).2 (hsq p (mem_filter.mp hp).1)]
  rw [he,sum_const,nsmul_eq_mul]
  have hr : (count P n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hcount
  change (count P n : ℝ)*(1/count P n)=1
  field_simp

theorem weighted_identity (P : Finset ℕ) (n : ℕ) (f : ℕ → ℂ)
    (hf : ∀ a b, f (a*b)=f a*f b) :
    (∑ p ∈ factors P n, f p*f (n/p)/((count P (n/p)+1 : ℕ) : ℂ)) = (weight P n : ℂ)*f n := by
  rw [weight,Complex.ofReal_sum,sum_mul]
  apply sum_congr rfl
  intro p hp
  rw [← hf,Nat.mul_div_cancel' (mem_filter.mp hp).2]
  push_cast
  ring

theorem weighted_ramare_sum (S P : Finset ℕ) (X : ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ X) (f : ℕ → ℂ)
    (hf : ∀ a b, f (a*b)=f a*f b) :
    (∑ n ∈ S, (weight P n : ℂ)*f n) =
      ∑ p ∈ P, ∑ m ∈ Icc 1 (X/p),
        if p*m ∈ S then f p*f m/((count P m+1 : ℕ) : ℂ) else 0 := by
  calc
    _ = ∑ n ∈ S, ∑ p ∈ factors P n, f p*f (n/p)/((count P (n/p)+1 : ℕ) : ℂ) := by
      apply sum_congr rfl
      intro n hn
      exact (weighted_identity P n f hf).symm
    _ = ∑ p ∈ P, ∑ n ∈ S.filter (p ∣ ·), f p*f (n/p)/((count P (n/p)+1 : ℕ) : ℂ) := by
      simp only [factors,sum_filter]
      rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro p hp
      rw [sum_multiples S X p (hP p hp).pos hS]
      apply sum_congr rfl
      intro m hm
      rw [Nat.mul_div_cancel_left m (hP p hp).pos]

theorem full_ramare_with_remainder (S P : Finset ℕ) (X : ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ X) (f : ℕ → ℂ)
    (hf : ∀ a b, f (a*b)=f a*f b) :
    (∑ n ∈ S, f n) =
      (∑ p ∈ P, ∑ m ∈ Icc 1 (X/p),
        if p*m ∈ S then f p*f m/((count P m+1 : ℕ) : ℂ) else 0) +
      ∑ n ∈ S, ((1-weight P n : ℝ) : ℂ)*f n := by
  rw [← weighted_ramare_sum S P X hP hS f hf,← sum_add_distrib]
  apply sum_congr rfl
  intro n hn
  push_cast
  ring

theorem residual_nonneg (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n : ℕ) : 0 ≤ 1-weight P n :=
  sub_nonneg.mpr (weight_le_one P hP n)

theorem residual_le_one (P : Finset ℕ) (n : ℕ) : 1-weight P n ≤ 1 := by
  have h := weight_nonneg P n
  linarith

theorem residual_good_zero (N : ℕ) (hN : 0 < N) (n : ℕ) (hn : n ∈ SlowPrimeBandSieve.good N) :
    1-weight (SlowPrimeBandSieve.primes N) n=0 := by
  have hs := SlowPrimeBandSieve.good_support N hN n hn
  have hw : weight (SlowPrimeBandSieve.primes N) n=1 :=
    weight_eq_one (SlowPrimeBandSieve.primes N) (fun p hp ↦ (mem_filter.mp hp).2) n hs.2.1 hs.2.2
  rw [hw,sub_self]
end RamareWeights
