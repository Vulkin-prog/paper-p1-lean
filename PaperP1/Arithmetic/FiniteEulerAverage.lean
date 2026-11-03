module

public import PaperP1.Arithmetic.TruncatedKernelProducts
public import Mathlib.RingTheory.Coprime.Lemmas

/-! # The exact divisor expansion and first moment of a finite nonnegative Euler product -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteEulerAverage

open Finset

def localProduct (P : Finset ℕ) (h : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∏ p ∈ P.filter (fun p ↦ p ∣ n), (1 + h p)

theorem product_divides_iff (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (n : ℕ) :
    P.prod id ∣ n ↔ ∀ p ∈ P, p ∣ n := by
  constructor
  · exact fun hd p hp ↦ (dvd_prod_of_mem id hp).trans hd
  · intro hd
    apply Finset.prod_dvd_of_isRelPrime _ hd
    intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hP p hp) (hP q hq)).mpr hpq)

theorem localProduct_expand (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (h : ℕ → ℝ) (n : ℕ) :
    localProduct P h n = ∑ S ∈ P.powerset, if S.prod id ∣ n then ∏ p ∈ S, h p else 0 := by
  have hfilter : (P.filter (fun p ↦ p ∣ n)).powerset = P.powerset.filter (fun S ↦ S.prod id ∣ n) := by
    ext S
    simp only [mem_powerset, mem_filter]
    constructor
    · intro hS
      have hSP : S ⊆ P := fun p hp ↦ (mem_filter.mp (hS hp)).1
      exact ⟨hSP, (product_divides_iff S (fun p hp ↦ hP p (hSP hp)) n).mpr
        (fun p hp ↦ (mem_filter.mp (hS hp)).2)⟩
    · rintro ⟨hSP, hd⟩ p hp
      exact mem_filter.mpr ⟨hSP hp, (dvd_prod_of_mem id hp).trans hd⟩
  rw [localProduct, prod_one_add, hfilter, sum_filter]

theorem exact_average (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (h : ℕ → ℝ) (X : ℕ) :
    (∑ n ∈ Ioc 0 X, localProduct P h n) =
      ∑ S ∈ P.powerset, ((X / S.prod id : ℕ) : ℝ) * ∏ p ∈ S, h p := by
  simp_rw [localProduct_expand P hP h]
  rw [sum_comm]
  apply sum_congr rfl
  intro S _
  rw [← sum_filter, sum_const, nsmul_eq_mul, Nat.Ioc_filter_dvd_card_eq_div]

theorem average_bound (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (h : ℕ → ℝ)
    (hh : ∀ p ∈ P, 0 ≤ h p) (X : ℕ) :
    (∑ n ∈ Ioc 0 X, localProduct P h n) ≤ (X : ℝ) * ∏ p ∈ P, (1 + h p / p) := by
  rw [exact_average P hP h X]
  calc
    _ ≤ ∑ S ∈ P.powerset, ((X : ℝ) / ((S.prod id : ℕ) : ℝ)) * ∏ p ∈ S, h p := by
      apply sum_le_sum
      intro S hS
      exact mul_le_mul_of_nonneg_right Nat.cast_div_le
        (prod_nonneg fun p hp ↦ hh p (mem_powerset.mp hS hp))
    _ = (X : ℝ) * ∑ S ∈ P.powerset, ∏ p ∈ S, h p / p := by
      rw [mul_sum]
      apply sum_congr rfl
      intro S _
      rw [prod_div_distrib, Nat.cast_prod]
      simp only [id_eq]
      ring
    _ = _ := by rw [← prod_one_add]

end PaperP1.FiniteEulerAverage
