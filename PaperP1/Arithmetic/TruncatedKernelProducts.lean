module

public import PaperP1.Arithmetic.RankinSmallKernel
public import PaperP1.Arithmetic.EvenSquareClasses
public import PaperP1.Arithmetic.PrimeProductBudget
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Data.Nat.Dist

/-! # Literal prime supports and coprime products of truncated odd kernels -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TruncatedKernelProducts

open Finset PaperP1.Arithmetic PaperP1.DefectivePredicate PaperP1.LargeOddKernel
open PaperP1.RankinSmallKernel PaperP1.Affine

def support (Y : ℝ) (n : ℕ) : Finset ℕ :=
  (oddPrimeSupport n).filter fun p : ℕ ↦ Y < (p : ℝ)

theorem kernel_eq_prod (Y : ℝ) (n : ℕ) : truncatedKernel Y n = (support Y n).prod id := rfl

theorem prime_of_mem_support {Y : ℝ} {n p : ℕ} (hp : p ∈ support Y n) : Nat.Prime p :=
  prime_of_mem_oddPrimeSupport (mem_filter.mp hp).1

theorem dvd_of_mem_oddPrimeSupport {n p : ℕ} (hp : p ∈ oddPrimeSupport n) : p ∣ n := by
  have hs : p ∈ n.factorization.support := Finsupp.support_mapRange hp
  exact (Nat.mem_primeFactors.mp hs).2.1

theorem kernel_pos (Y : ℝ) (n : ℕ) : 0 < truncatedKernel Y n := by
  exact prod_pos (fun p hp ↦ (prime_of_mem_support hp).pos)

theorem kernel_dvd (Y : ℝ) (n : ℕ) : truncatedKernel Y n ∣ n := by
  by_cases hn : n = 0
  · rw [hn]
    exact dvd_zero _
  have hsub : support Y n ⊆ oddPrimeSupport n := filter_subset _ _
  have hprod : (support Y n).prod id ∣ (oddPrimeSupport n).prod id :=
    prod_dvd_prod_of_subset _ _ id hsub
  have hfull : (oddPrimeSupport n).prod id ∣ n :=
    ⟨canonicalSquarePart n ^ 2, canonical_odd_mul_sq_decomposition hn⟩
  exact hprod.trans hfull

theorem kernel_le (Y : ℝ) (n : ℕ) (hn : 0 < n) : truncatedKernel Y n ≤ n :=
  Nat.le_of_dvd hn (kernel_dvd Y n)

theorem prime_dvd_kernel_iff (Y : ℝ) (n p : ℕ) (hp : Nat.Prime p) :
    p ∣ truncatedKernel Y n ↔ p ∈ support Y n := by
  constructor
  · intro hdvd
    obtain ⟨q, hq, hpq⟩ := (hp.prime.dvd_finsetProd_iff id).mp hdvd
    have heq : p = q := (Nat.prime_dvd_prime_iff_eq hp (prime_of_mem_support hq)).mp hpq
    exact heq ▸ hq
  · exact fun h ↦ dvd_prod_of_mem id h

theorem kernel_squarefree (Y : ℝ) (n : ℕ) : Squarefree (truncatedKernel Y n) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    apply Nat.coprime_iff_isRelPrime.mp
    exact (Nat.coprime_primes (prime_of_mem_support hp) (prime_of_mem_support hq)).mpr hpq
  · intro p hp
    exact (prime_of_mem_support hp).squarefree

theorem primeFactors_kernel (Y : ℝ) (n : ℕ) : (truncatedKernel Y n).primeFactors = support Y n := by
  ext p
  constructor
  · intro hp
    obtain ⟨hpprime, hpdvd, _⟩ := Nat.mem_primeFactors.mp hp
    exact (prime_dvd_kernel_iff Y n p hpprime).mp hpdvd
  · intro hp
    exact Nat.mem_primeFactors.mpr ⟨prime_of_mem_support hp,
      (prime_dvd_kernel_iff Y n p (prime_of_mem_support hp)).mpr hp, (kernel_pos Y n).ne'⟩

theorem kernels_coprime (Y : ℝ) (n m : ℕ) (hnm : n ≠ m) (hdist : (Nat.dist n m : ℝ) ≤ Y) :
    Nat.Coprime (truncatedKernel Y n) (truncatedKernel Y m) := by
  apply Nat.coprime_of_dvd
  intro p hp hpn hpm
  have hpSupport := (prime_dvd_kernel_iff Y n p hp).mp hpn
  have hpY : Y < (p : ℝ) := (mem_filter.mp hpSupport).2
  have hpn' : p ∣ n := hpn.trans (kernel_dvd Y n)
  have hpm' : p ∣ m := hpm.trans (kernel_dvd Y m)
  have hpdist : p ∣ Nat.dist n m := by
    rcases le_total n m with h | h
    · simpa only [Nat.dist_eq_sub_of_le h] using Nat.dvd_sub hpm' hpn'
    · simpa only [Nat.dist_eq_sub_of_le_right h] using Nat.dvd_sub hpn' hpm'
  have hpbound : p ≤ Nat.dist n m := Nat.le_of_dvd (Nat.dist_pos_of_ne hnm) hpdist
  have hpboundR : (p : ℝ) ≤ Nat.dist n m := by exact_mod_cast hpbound
  linarith

theorem window_kernels_coprime (x L : ℕ) (hx : 2 ≤ x) (Y : ℝ)
    (hY : (L + 1 : ℝ) ≤ Y) (u v : Fin (L + 1)) (huv : u ≠ v) :
    Nat.Coprime (truncatedKernel Y (startCompleteVertexLabel x L u))
      (truncatedKernel Y (startCompleteVertexLabel x L v)) := by
  have hxpos : 0 < x := by omega
  have hne : startCompleteVertexLabel x L u ≠ startCompleteVertexLabel x L v :=
    fun h ↦ huv (startCompleteVertexLabel_injective hxpos h)
  have hdist : Nat.dist (startCompleteVertexLabel x L u) (startCompleteVertexLabel x L v) ≤ L + 1 := by
    rw [startCompleteVertexLabel_eq_offset hxpos, startCompleteVertexLabel_eq_offset hxpos]
    have hu := u.isLt
    have hv := v.isLt
    rcases le_total (x - 1 + u.val) (x - 1 + v.val) with h | h
    · rw [Nat.dist_eq_sub_of_le h]
      omega
    · rw [Nat.dist_eq_sub_of_le_right h]
      omega
  apply kernels_coprime Y _ _ hne
  exact (by exact_mod_cast hdist : (Nat.dist (startCompleteVertexLabel x L u)
    (startCompleteVertexLabel x L v) : ℝ) ≤ (L + 1 : ℕ)).trans (by simpa only [Nat.cast_add, Nat.cast_one] using hY)

theorem kernel_pair_squarefree (Y : ℝ) (n m : ℕ) (hnm : n ≠ m) (hdist : (Nat.dist n m : ℝ) ≤ Y) :
    Squarefree (truncatedKernel Y n * truncatedKernel Y m) :=
  squarefree_mul_iff.mpr ⟨Nat.coprime_iff_isRelPrime.mp (kernels_coprime Y n m hnm hdist),
    kernel_squarefree Y n, kernel_squarefree Y m⟩

theorem kernel_pair_prime_above (Y : ℝ) (n m p : ℕ)
    (hp : p ∈ (truncatedKernel Y n * truncatedKernel Y m).primeFactors) : Y < (p : ℝ) := by
  rw [Nat.primeFactors_mul (kernel_pos Y n).ne' (kernel_pos Y m).ne',
    primeFactors_kernel, primeFactors_kernel] at hp
  rcases mem_union.mp hp with hp | hp
  · exact (mem_filter.mp hp).2
  · exact (mem_filter.mp hp).2

theorem kernel_pair_upper (Y : ℝ) (n m N : ℕ) (hn : 0 < n) (hm : 0 < m)
    (hnN : n ≤ 3 * N) (hmN : m ≤ 3 * N) :
    truncatedKernel Y n * truncatedKernel Y m ≤ 9 * N ^ 2 := by
  calc
    _ ≤ n * m := Nat.mul_le_mul (kernel_le Y n hn) (kernel_le Y m hm)
    _ ≤ (3 * N) * (3 * N) := Nat.mul_le_mul hnN hmN
    _ = _ := by ring

theorem kernel_pair_card_le_assignmentExponent (Y : ℝ) (hY : 1 < Y) (n m N : ℕ)
    (hn : 0 < n) (hm : 0 < m) (hnm : n ≠ m) (hdist : (Nat.dist n m : ℝ) ≤ Y)
    (hnN : n ≤ 3 * N) (hmN : m ≤ 3 * N) :
    (truncatedKernel Y n * truncatedKernel Y m).primeFactors.card ≤
      PaperP1.PrimeProductBudget.assignmentExponent N Y := by
  let Q := truncatedKernel Y n * truncatedKernel Y m
  have hsq : Squarefree Q := kernel_pair_squarefree Y n m hnm hdist
  have hprod : Q.primeFactors.prod id = Q := Nat.prod_primeFactors_of_squarefree hsq
  apply PaperP1.PrimeProductBudget.card_le_assignmentExponent Q.primeFactors N Y hY
  · intro p hp
    exact ⟨Nat.prime_of_mem_primeFactors hp, kernel_pair_prime_above Y n m p hp⟩
  · rw [hprod]
    exact kernel_pair_upper Y n m N hn hm hnN hmN

theorem kernel_pair_gt_square (Y : ℝ) (n m : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (hn : T < (truncatedKernel Y n : ℝ)) (hm : T < (truncatedKernel Y m : ℝ)) :
    T ^ 2 < (truncatedKernel Y n * truncatedKernel Y m : ℕ) := by
  have hpos : (0 : ℝ) < truncatedKernel Y n := by exact_mod_cast kernel_pos Y n
  have h₁ : T * T ≤ (truncatedKernel Y n : ℝ) * T := mul_le_mul_of_nonneg_right hn.le hT
  have h₂ := mul_lt_mul_of_pos_left hm hpos
  simpa only [pow_two, Nat.cast_mul] using h₁.trans_lt h₂

end PaperP1.TruncatedKernelProducts
