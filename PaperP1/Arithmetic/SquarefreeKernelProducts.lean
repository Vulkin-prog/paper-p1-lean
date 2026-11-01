module

public import PaperP1.Arithmetic.SplitOffsetSupports
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Algebra.BigOperators.Associated

/-! # Exact multiplication and overlap identities for canonical squarefree kernels -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SquarefreeKernelProducts

open Finset PaperP1.SmallPrimeBudget PaperP1.DefectivePredicate PaperP1.LargeOddKernel
open scoped symmDiff

def overlap (a b : ℕ) : ℕ := (oddPrimeSupport a ∩ oddPrimeSupport b).prod id

theorem mem_support_iff (n p : ℕ) : p ∈ oddPrimeSupport n ↔ n.factorization p % 2 ≠ 0 := by
  simp only [oddPrimeSupport, oddFactorization, Finsupp.mem_support_iff, Finsupp.mapRange_apply]

theorem support_mul (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    oddPrimeSupport (a * b) = oddPrimeSupport a ∆ oddPrimeSupport b := by
  ext p
  rw [mem_support_iff, mem_symmDiff, mem_support_iff, mem_support_iff,
    Nat.factorization_mul ha hb, Finsupp.add_apply]
  omega

theorem support_square (a : ℕ) : oddPrimeSupport (a ^ 2) = ∅ := by
  ext p
  rw [mem_oddPrimeSupport_iff_parityVec_ne_zero, PaperP1.Arithmetic.parityVec_pow_two]
  simp

theorem kernel_mul_square (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    squarefreeKernel (a * b ^ 2) = squarefreeKernel a := by
  unfold squarefreeKernel
  rw [support_mul a (b ^ 2) ha (pow_ne_zero _ hb), support_square]
  simp only [Finset.symmDiff_def, sdiff_empty, empty_sdiff, union_empty]

theorem support_product_identity (S T : Finset ℕ) :
    S.prod id * T.prod id = (S ∆ T).prod id * (S ∩ T).prod id ^ 2 := by
  have h := prod_union_inter (s₁ := S) (s₂ := T) (f := id)
  have hunion : (S ∆ T) ∪ (S ∩ T) = S ∪ T := symmDiff_sup_inf S T
  have hdis : Disjoint (S ∆ T) (S ∩ T) := by
    simpa only [inf_eq_inter] using disjoint_symmDiff_inf S T
  rw [← hunion, prod_union hdis] at h
  nlinarith only [h]

theorem kernel_mul_overlap (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    squarefreeKernel a * squarefreeKernel b = squarefreeKernel (a * b) * overlap a b ^ 2 := by
  unfold squarefreeKernel overlap
  rw [support_mul a b ha hb]
  exact support_product_identity _ _

theorem overlap_pos (a b : ℕ) : 0 < overlap a b := by
  apply prod_pos
  intro p hp
  exact (prime_of_mem_oddPrimeSupport (mem_inter.mp hp).1).pos

theorem overlap_dvd_of_prime_divisibility (a b M : ℕ)
    (hM : ∀ p ∈ oddPrimeSupport a ∩ oddPrimeSupport b, p ∣ M) : overlap a b ∣ M := by
  apply Finset.prod_primes_dvd
  · intro p hp
    exact (prime_of_mem_oddPrimeSupport (mem_inter.mp hp).1).prime
  · exact hM

theorem support_of_squarefree (n : ℕ) (hn : Squarefree n) : oddPrimeSupport n = n.primeFactors := by
  ext p
  constructor
  · intro hp
    exact Finsupp.support_mapRange hp
  · intro hp
    rw [mem_support_iff, Nat.factorization_eq_one_of_squarefree hn
      (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)]
    norm_num

theorem kernel_of_squarefree (n : ℕ) (hn : Squarefree n) : squarefreeKernel n = n := by
  unfold squarefreeKernel
  rw [support_of_squarefree n hn]
  exact Nat.prod_primeFactors_of_squarefree hn

theorem squarefreeKernel_pos (n : ℕ) : 0 < squarefreeKernel n := by
  exact prod_pos (fun p hp ↦ (prime_of_mem_oddPrimeSupport hp).pos)

theorem canonical_part_ne_zero (n : ℕ) (hn : n ≠ 0) : canonicalSquarePart n ≠ 0 := by
  intro hz
  have hr := squarefreeKernel_mul_squarePart hn
  rw [hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] at hr
  exact hn hr.symm

theorem finite_product_decomposition {ι : Type*} (S : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ S, f i ≠ 0) :
    (∏ i ∈ S, f i) = (∏ i ∈ S, squarefreeKernel (f i)) *
      (∏ i ∈ S, canonicalSquarePart (f i)) ^ 2 := by
  calc
    _ = ∏ i ∈ S, (squarefreeKernel (f i) * canonicalSquarePart (f i) ^ 2) := by
      apply prod_congr rfl
      intro i hi
      exact (squarefreeKernel_mul_squarePart (hf i hi)).symm
    _ = _ := by rw [prod_mul_distrib, ← prod_pow]

theorem kernel_product_kernels {ι : Type*} (S : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ S, f i ≠ 0) :
    squarefreeKernel (∏ i ∈ S, squarefreeKernel (f i)) = squarefreeKernel (∏ i ∈ S, f i) := by
  have hK : (∏ i ∈ S, squarefreeKernel (f i)) ≠ 0 :=
    (prod_pos (fun i _ ↦ squarefreeKernel_pos (f i))).ne'
  have hP : (∏ i ∈ S, canonicalSquarePart (f i)) ≠ 0 :=
    prod_ne_zero_iff.mpr (fun i hi ↦ canonical_part_ne_zero (f i) (hf i hi))
  rw [finite_product_decomposition S f hf, kernel_mul_square _ _ hK hP]

end PaperP1.SquarefreeKernelProducts
