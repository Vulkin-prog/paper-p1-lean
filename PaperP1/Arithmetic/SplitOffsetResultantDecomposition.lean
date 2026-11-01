module

public import PaperP1.Arithmetic.SquarefreeKernelProducts
public import PaperP1.Diophantine.LinearKernelFibres

/-! # The exact square-overlap factor divides the actual difference resultant -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SplitOffsetResultantDecomposition

open Finset PaperP1.SplitOffsetProducts PaperP1.SquarefreeKernelProducts
open PaperP1.LinearKernelFibres PaperP1.SmallPrimeBudget PaperP1.DefectivePredicate
open PaperP1.LargeOddKernel

theorem resultant_eq_nested (A : Finset ℤ) :
    resultant A = ∏ a ∈ A, ∏ b ∈ A, if a < b then (a - b).natAbs else 1 := by
  unfold resultant pairs
  rw [prod_filter, prod_product]

theorem resultant_insert_max (A : Finset ℤ) (a : ℤ) (hmax : ∀ b ∈ A, b < a) :
    resultant (insert a A) = resultant A * ∏ b ∈ A, (b - a).natAbs := by
  have ha : a ∉ A := by intro ha; exact (lt_irrefl a) (hmax a ha)
  rw [resultant_eq_nested, prod_insert ha]
  have htop : (∏ b ∈ insert a A, if a < b then (a - b).natAbs else 1) = 1 := by
    apply prod_eq_one
    intro b hb
    have hba : b ≤ a := by
      obtain hba | hbA := mem_insert.mp hb
      · exact hba.le
      · exact (hmax b hbA).le
    exact ite_eq_right (not_lt_of_ge hba)
  rw [htop, one_mul]
  calc
    _ = ∏ b ∈ A, ((b - a).natAbs * ∏ d ∈ A, if b < d then (b - d).natAbs else 1) := by
      apply prod_congr rfl
      intro b hb
      rw [prod_insert ha, ite_eq_left (hmax b hb)]
    _ = (∏ b ∈ A, (b - a).natAbs) * resultant A := by
      rw [prod_mul_distrib, resultant_eq_nested]
    _ = _ := by ring

theorem overlap_divides_cross (A : Finset ℤ) (n : ℕ) (a : ℤ) :
    overlap (value n a) (product A n) ∣ ∏ b ∈ A, (b - a).natAbs := by
  apply overlap_dvd_of_prime_divisibility
  intro p hp
  obtain ⟨hpa, hpP⟩ := mem_inter.mp hp
  have hpprime := prime_of_mem_oddPrimeSupport hpa
  have hdiva := PaperP1.TruncatedKernelProducts.dvd_of_mem_oddPrimeSupport hpa
  have hdivP := PaperP1.TruncatedKernelProducts.dvd_of_mem_oddPrimeSupport hpP
  change p ∣ ∏ b ∈ A, value n b at hdivP
  obtain ⟨b, hb, hdivb⟩ := (hpprime.prime.dvd_finsetProd_iff (fun b ↦ value n b)).mp hdivP
  have hd := dvd_sub (Int.natCast_dvd.mpr hdivb) (Int.natCast_dvd.mpr hdiva)
  have heq : ((n : ℤ) + b) - ((n : ℤ) + a) = b - a := by ring
  rw [heq] at hd
  exact (Int.natCast_dvd.mp hd).trans (dvd_prod_of_mem (fun b : ℤ ↦ (b - a).natAbs) hb)

theorem linear_product_decomposition (A : Finset ℤ) (n : ℕ)
    (hvalues : ∀ a ∈ A, (n : ℤ) + a ≠ 0) :
    ∃ R : ℕ, R ∣ resultant A ∧ (∏ a ∈ A, linearKernel n a) = kernel A n * R ^ 2 := by
  induction A using Finset.induction_on_max with
  | empty =>
    refine ⟨1, one_dvd _, ?_⟩
    have h1 := kernel_of_squarefree 1 (by simp)
    simpa only [prod_empty, kernel, product, one_pow, mul_one] using h1.symm
  | insert a A hmax ih =>
    have ha : a ∉ A := by intro ha; exact (lt_irrefl a) (hmax a ha)
    have hrest : ∀ b ∈ A, (n : ℤ) + b ≠ 0 := fun b hb ↦ hvalues b (mem_insert_of_mem hb)
    obtain ⟨R, hRD, hR⟩ := ih hrest
    have hva : value n a ≠ 0 := Int.natAbs_ne_zero.mpr (hvalues a (mem_insert_self a A))
    have hvP : product A n ≠ 0 := prod_ne_zero_iff.mpr
      (fun b hb ↦ Int.natAbs_ne_zero.mpr (hrest b hb))
    have hmul := kernel_mul_overlap (value n a) (product A n) hva hvP
    have hk : linearKernel n a * kernel A n = kernel (insert a A) n *
        overlap (value n a) (product A n) ^ 2 := by
      simpa only [linearKernel, kernel, product, prod_insert ha, value] using hmul
    refine ⟨overlap (value n a) (product A n) * R, ?_, ?_⟩
    · rw [resultant_insert_max A a hmax, mul_comm (resultant A)]
      exact Nat.mul_dvd_mul (overlap_divides_cross A n a) hRD
    · rw [prod_insert ha, hR]
      calc
        _ = (linearKernel n a * kernel A n) * R ^ 2 := by ring
        _ = _ := by rw [hk]; ring

theorem linear_product_divides_kernel_resultant_square (A : Finset ℤ) (n : ℕ)
    (hvalues : ∀ a ∈ A, (n : ℤ) + a ≠ 0) :
    (∏ a ∈ A, linearKernel n a) ∣ kernel A n * resultant A ^ 2 := by
  obtain ⟨R, hRD, hR⟩ := linear_product_decomposition A n hvalues
  rw [hR]
  exact Nat.mul_dvd_mul_left (kernel A n) (pow_dvd_pow_of_dvd hRD 2)

end PaperP1.SplitOffsetResultantDecomposition
