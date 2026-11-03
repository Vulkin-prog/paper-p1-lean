module

public import PaperP1.Arithmetic.TruncatedKernelProducts
public import Mathlib.Data.Nat.Factorization.Basic

/-! # The actual cutoff-dependent square part and the full smooth part of a positive integer -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CutoffSquareParts

open Finset PaperP1.Arithmetic PaperP1.LargeOddKernel PaperP1.DefectivePredicate

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def smallPart (Y n : ℕ) : ℕ :=
  (n.primeFactors.filter fun p ↦ p ≤ Y).prod fun p ↦ p ^ n.factorization p

def largeSquarePart (Y n : ℕ) : ℕ :=
  (n.primeFactors.filter fun p ↦ Y < p).prod fun p ↦ p ^ (n.factorization p / 2)

def quotient (Y n : ℕ) : ℕ := smallPart Y n * largeSquarePart Y n ^ 2

theorem small_part_pos (Y n : ℕ) : 0 < smallPart Y n := by
  apply prod_pos
  intro p hp
  exact pow_pos (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1).pos _

theorem large_square_part_pos (Y n : ℕ) : 0 < largeSquarePart Y n := by
  apply prod_pos
  intro p hp
  exact pow_pos (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1).pos _

theorem odd_support_eq (n : ℕ) :
    oddPrimeSupport n = n.primeFactors.filter fun p ↦ n.factorization p % 2 = 1 := by
  ext p
  have hparity : p ∈ oddPrimeSupport n ↔ n.factorization p % 2 = 1 := by
    rw [mem_oddPrimeSupport_iff_parityVec_ne_zero]
    simp only [parityVec_apply, ne_eq, ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]
    omega
  rw [mem_filter, hparity]
  constructor
  · intro h
    exact ⟨by change p ∈ n.factorization.support; rw [Finsupp.mem_support_iff]; omega, h⟩
  · exact fun h ↦ h.2

theorem kernel_product (Y n : ℕ) :
    largeOddKernel Y n =
      (n.primeFactors.filter fun p ↦ Y < p).prod fun p ↦ p ^ (n.factorization p % 2) := by
  unfold largeOddKernel
  rw [odd_support_eq, filter_filter, prod_filter, prod_filter]
  apply prod_congr rfl
  intro p _hp
  rcases Nat.mod_two_eq_zero_or_one (n.factorization p) with hzero | hone
  · simp only [hzero, zero_ne_one, false_and, ite_false, pow_zero, ite_self]
  · simp only [hone, true_and, pow_one, id_eq]

theorem decomposition (Y n : ℕ) (hn : 0 < n) :
    n = smallPart Y n * largeSquarePart Y n ^ 2 * largeOddKernel Y n := by
  let P := n.primeFactors.filter fun p ↦ p ≤ Y
  let Q := n.primeFactors.filter fun p ↦ Y < p
  have hPQ : P ∪ Q = n.primeFactors := by
    ext p
    simp only [P, Q, mem_union, mem_filter, ← and_or_left, le_or_gt, and_true]
  have hdis : Disjoint P Q := by
    apply disjoint_left.mpr
    exact fun _ hp hq ↦ (not_lt_of_ge (mem_filter.mp hp).2) (mem_filter.mp hq).2
  have hrep := Nat.prod_primeFactors_pow_factorization hn.ne'
  rw [← hPQ, prod_union hdis] at hrep
  have hQ : Q.prod (fun p ↦ p ^ n.factorization p) = largeSquarePart Y n ^ 2 * largeOddKernel Y n := by
    rw [kernel_product, largeSquarePart, ← Finset.prod_pow, ← prod_mul_distrib]
    apply prod_congr rfl
    intro p _hp
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  rw [hQ] at hrep
  simpa only [smallPart, P, mul_assoc] using hrep

theorem quotient_pos (Y n : ℕ) : 0 < quotient Y n :=
  Nat.mul_pos (small_part_pos Y n) (pow_pos (large_square_part_pos Y n) _)

theorem quotient_mul_kernel (Y n : ℕ) (hn : 0 < n) : quotient Y n * largeOddKernel Y n = n :=
  (decomposition Y n hn).symm

theorem quotient_dvd (Y n : ℕ) (hn : 0 < n) : quotient Y n ∣ n :=
  ⟨largeOddKernel Y n, (quotient_mul_kernel Y n hn).symm⟩

theorem quotient_eq_div (Y n : ℕ) (hn : 0 < n) : quotient Y n = n / largeOddKernel Y n := by
  have hp := PaperP1.SmallPrimeBudget.largeOddKernel_pos Y n
  calc
    _ = (quotient Y n * largeOddKernel Y n) / largeOddKernel Y n :=
      (Nat.mul_div_cancel _ hp).symm
    _ = _ := congrArg (fun t : ℕ ↦ t / largeOddKernel Y n) (quotient_mul_kernel Y n hn)

theorem prime_dvd_small_part {Y n p : ℕ} (hp : p.Prime) (hd : p ∣ smallPart Y n) : p ≤ Y := by
  obtain ⟨q, hq, hpq⟩ := (hp.prime.dvd_finsetProd_iff (fun q ↦ q ^ n.factorization q)).mp hd
  have hqprime := Nat.prime_of_mem_primeFactors (mem_filter.mp hq).1
  have heq : p = q := (Nat.prime_dvd_prime_iff_eq hp hqprime).mp (hp.dvd_of_dvd_pow hpq)
  subst p
  exact (mem_filter.mp hq).2

theorem prime_dvd_large_square {Y n p : ℕ} (hp : p.Prime) (hd : p ∣ largeSquarePart Y n) :
    Y < p ∧ p ∣ n := by
  obtain ⟨q, hq, hpq⟩ := (hp.prime.dvd_finsetProd_iff (fun q ↦ q ^ (n.factorization q / 2))).mp hd
  have hqprime := Nat.prime_of_mem_primeFactors (mem_filter.mp hq).1
  have heq : p = q := (Nat.prime_dvd_prime_iff_eq hp hqprime).mp (hp.dvd_of_dvd_pow hpq)
  subst p
  exact ⟨(mem_filter.mp hq).2, Nat.dvd_of_mem_primeFactors (mem_filter.mp hq).1⟩

theorem large_square_dvd (Y n : ℕ) (hn : 0 < n) : largeSquarePart Y n ^ 2 ∣ n := by
  refine ⟨smallPart Y n * largeOddKernel Y n, ?_⟩
  exact (decomposition Y n hn).trans (by ring)

theorem large_square_parts_coprime {Y n m : ℕ} (hnm : n ≠ m) (hdist : Nat.dist n m ≤ Y) :
    Nat.Coprime (largeSquarePart Y n) (largeSquarePart Y m) := by
  apply Nat.coprime_of_dvd
  intro p hp hpn hpm
  obtain ⟨hpY, hpn⟩ := prime_dvd_large_square hp hpn
  have hpm := (prime_dvd_large_square hp hpm).2
  have hpd : p ∣ Nat.dist n m := by
    rcases le_total n m with h | h
    · simpa only [Nat.dist_eq_sub_of_le h] using Nat.dvd_sub hpm hpn
    · simpa only [Nat.dist_eq_sub_of_le_right h] using Nat.dvd_sub hpn hpm
  have hle := (Nat.le_of_dvd (Nat.dist_pos_of_ne hnm) hpd).trans hdist
  omega

theorem small_large_coprime (Y n m : ℕ) : Nat.Coprime (smallPart Y n) (largeSquarePart Y m) := by
  apply Nat.coprime_of_dvd
  intro p hp hsmall hlarge
  have hlo := prime_dvd_small_part hp hsmall
  have hhi := (prime_dvd_large_square hp hlarge).1
  omega

theorem kernel_one_of_smooth_square (Y s a : ℕ) (hs : 0 < s) (ha : 0 < a)
    (hsmooth : ∀ p : ℕ, p.Prime → p ∣ s → p ≤ Y) : largeOddKernel Y (s * a ^ 2) = 1 := by
  apply (largeOddKernel_eq_one_iff Y _).mpr
  intro p hp hYp
  rw [parityVec_mul hs.ne' (pow_ne_zero _ ha.ne'), parityVec_pow_two, add_zero]
  by_contra hparity
  have hdiv := PaperP1.TruncatedKernelProducts.dvd_of_mem_oddPrimeSupport
    (mem_oddPrimeSupport_iff_parityVec_ne_zero.mpr hparity)
  exact (not_le_of_gt hYp) (hsmooth p hp hdiv)

theorem quotient_kernel_one (Y n : ℕ) : largeOddKernel Y (quotient Y n) = 1 :=
  kernel_one_of_smooth_square Y _ _ (small_part_pos Y n) (large_square_part_pos Y n)
    (fun _ hp hd ↦ prime_dvd_small_part hp hd)

theorem square_kernel_one (Y a : ℕ) : largeOddKernel Y (a ^ 2) = 1 := by
  apply (largeOddKernel_eq_one_iff Y _).mpr
  intro p _hp _hYp
  rw [parityVec_pow_two, Finsupp.zero_apply]

end PaperP1.CutoffSquareParts
