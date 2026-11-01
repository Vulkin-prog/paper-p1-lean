module

public import PaperP1.Arithmetic.SmallPrimeBudget
public import PaperP1.Diophantine.QuadraticKernelFibres
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Data.Finset.Prod

/-! # Literal integer-offset products and their difference resultant -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SplitOffsetProducts

open Finset PaperP1.SmallPrimeBudget PaperP1.DefectivePredicate PaperP1.LargeOddKernel

def product (A : Finset ℤ) (n : ℕ) : ℕ := ∏ a ∈ A, ((n : ℤ) + a).natAbs
def pairs (A : Finset ℤ) : Finset (ℤ × ℤ) := (A ×ˢ A).filter fun ab ↦ ab.1 < ab.2
def resultant (A : Finset ℤ) : ℕ := ∏ ab ∈ pairs A, (ab.1 - ab.2).natAbs
def kernel (A : Finset ℤ) (n : ℕ) : ℕ := squarefreeKernel (product A n)

theorem mem_pairs (A : Finset ℤ) (a b : ℤ) :
    (a, b) ∈ pairs A ↔ a ∈ A ∧ b ∈ A ∧ a < b := by
  simp only [pairs, mem_filter, mem_product, and_assoc]

theorem card_pairs (A : Finset ℤ) : (pairs A).card ≤ A.card ^ 2 := by
  calc
    _ ≤ (A ×ˢ A).card := card_filter_le _ _
    _ = _ := by rw [card_product]; ring

theorem resultant_pos (A : Finset ℤ) : 0 < resultant A := by
  apply prod_pos
  intro ab hab
  have hlt := ((mem_pairs A ab.1 ab.2).mp hab).2.2
  exact Int.natAbs_pos.mpr (sub_ne_zero.mpr hlt.ne)

theorem resultant_le_pow (A : Finset ℤ) (W : ℕ) (hW : 0 < W)
    (hA : ∀ a ∈ A, a.natAbs ≤ W) : resultant A ≤ (2 * W) ^ (A.card ^ 2) := by
  have hlocal : ∀ ab ∈ pairs A, (ab.1 - ab.2).natAbs ≤ 2 * W := by
    intro ab hab
    obtain ⟨ha, hb, _⟩ := (mem_pairs A ab.1 ab.2).mp hab
    have htri := Int.natAbs_sub_le ab.1 ab.2
    have haW := hA ab.1 ha
    have hbW := hA ab.2 hb
    omega
  calc
    _ ≤ ∏ _ab ∈ pairs A, 2 * W := prod_le_prod hlocal
    _ = (2 * W) ^ (pairs A).card := by simp
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (card_pairs A)

theorem product_pos (A : Finset ℤ) (n W : ℕ) (hWn : W < n)
    (hA : ∀ a ∈ A, a.natAbs ≤ W) : 0 < product A n := by
  apply prod_pos
  intro a ha
  have habs : |a| ≤ (W : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast hA a ha
  have hlo := (abs_le.mp habs).1
  have hnl : (W : ℤ) < n := by exact_mod_cast hWn
  exact Int.natAbs_pos.mpr (by omega : (n : ℤ) + a ≠ 0)

theorem factor_pos (A : Finset ℤ) (n W : ℕ) (hWn : W < n)
    (hA : ∀ a ∈ A, a.natAbs ≤ W) (a : ℤ) (ha : a ∈ A) : 0 < (n : ℤ) + a := by
  have habs : |a| ≤ (W : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast hA a ha
  have hlo := (abs_le.mp habs).1
  have hnl : (W : ℤ) < n := by exact_mod_cast hWn
  omega

theorem product_cast (A : Finset ℤ) (n W : ℕ) (hWn : W < n)
    (hA : ∀ a ∈ A, a.natAbs ≤ W) :
    (product A n : ℤ) = ∏ a ∈ A, ((n : ℤ) + a) := by
  unfold product
  push_cast
  apply prod_congr rfl
  intro a ha
  rw [abs_of_pos (factor_pos A n W hWn hA a ha)]

theorem product_le_pow (A : Finset ℤ) (N n W : ℕ) (hn : n ≤ 2 * N) (hW : W ≤ N)
    (hA : ∀ a ∈ A, a.natAbs ≤ W) : product A n ≤ (3 * N) ^ A.card := by
  have hlocal : ∀ a ∈ A, ((n : ℤ) + a).natAbs ≤ 3 * N := by
    intro a ha
    have htri := Int.natAbs_add_le (n : ℤ) a
    rw [Int.natAbs_natCast] at htri
    have haW := hA a ha
    omega
  calc
    _ ≤ ∏ _a ∈ A, 3 * N := prod_le_prod hlocal
    _ = _ := by simp

theorem kernel_pos (A : Finset ℤ) (n : ℕ) : 0 < kernel A n := by
  apply prod_pos
  intro p hp
  exact (prime_of_mem_oddPrimeSupport hp).pos

theorem kernel_dvd (A : Finset ℤ) (n : ℕ) (hpos : 0 < product A n) : kernel A n ∣ product A n :=
  ⟨canonicalSquarePart (product A n) ^ 2, (squarefreeKernel_mul_squarePart hpos.ne').symm⟩

theorem kernel_le (A : Finset ℤ) (n : ℕ) (hpos : 0 < product A n) : kernel A n ≤ product A n :=
  Nat.le_of_dvd hpos (kernel_dvd A n hpos)

theorem kernel_squarefree (A : Finset ℤ) (n : ℕ) : Squarefree (kernel A n) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (prime_of_mem_oddPrimeSupport hp) (prime_of_mem_oddPrimeSupport hq)).mpr hpq)
  · intro p hp
    exact (prime_of_mem_oddPrimeSupport hp).squarefree

theorem kernel_resultant_log_height (A : Finset ℤ) (N n W : ℕ) (_hN : 0 < N)
    (hW : 0 < W) (hWn : W < n) (hn : n ≤ 2 * N) (hWN : W ≤ N)
    (hA : ∀ a ∈ A, a.natAbs ≤ W) :
    Real.log (kernel A n * resultant A) ≤
      (A.card : ℝ) * Real.log (3 * N) + (A.card : ℝ) ^ 2 * Real.log (2 * W) := by
  have hp := product_pos A n W hWn hA
  have hk := (kernel_le A n hp).trans (product_le_pow A N n W hn hWN hA)
  have hres := resultant_le_pow A W hW hA
  have hkR : (kernel A n : ℝ) ≤ (3 * (N : ℝ)) ^ A.card := by exact_mod_cast hk
  have hrR : (resultant A : ℝ) ≤ (2 * (W : ℝ)) ^ (A.card ^ 2) := by exact_mod_cast hres
  have hklog := Real.log_le_log (by exact_mod_cast kernel_pos A n : (0 : ℝ) < kernel A n) hkR
  have hrlog := Real.log_le_log (by exact_mod_cast resultant_pos A : (0 : ℝ) < resultant A) hrR
  rw [Real.log_pow] at hklog hrlog
  push_cast at hrlog
  rw [Real.log_mul (by exact_mod_cast (kernel_pos A n).ne') (by exact_mod_cast (resultant_pos A).ne')]
  linarith

end PaperP1.SplitOffsetProducts
