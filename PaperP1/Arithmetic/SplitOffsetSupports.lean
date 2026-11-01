module

public import PaperP1.Arithmetic.SplitOffsetProducts
public import PaperP1.Arithmetic.TruncatedKernelProducts

/-! # Actual linear-kernel supports lie in rad(q*D_A) -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SplitOffsetSupports

open Finset PaperP1.SplitOffsetProducts PaperP1.SmallPrimeBudget PaperP1.DefectivePredicate
open PaperP1.LargeOddKernel PaperP1.Arithmetic

theorem prime_dvd_squarefreeKernel_iff (m p : ℕ) (hp : Nat.Prime p) :
    p ∣ squarefreeKernel m ↔ p ∈ oddPrimeSupport m := by
  constructor
  · intro hdiv
    obtain ⟨r, hr, hpr⟩ := (hp.prime.dvd_finsetProd_iff id).mp hdiv
    have heq : p = r := (Nat.prime_dvd_prime_iff_eq hp (prime_of_mem_oddPrimeSupport hr)).mp hpr
    exact heq ▸ hr
  · exact fun h ↦ dvd_prod_of_mem id h

theorem shared_prime_divides_resultant (A : Finset ℤ) (n p : ℕ) (a b : ℤ)
    (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b)
    (hpa : p ∣ ((n : ℤ) + a).natAbs) (hpb : p ∣ ((n : ℤ) + b).natAbs) :
    p ∣ resultant A := by
  have hdiff : (p : ℤ) ∣ a - b := by
    have hd := dvd_sub (Int.natCast_dvd.mpr hpa) (Int.natCast_dvd.mpr hpb)
    convert hd using 1
    ring
  have hd : p ∣ (a - b).natAbs := Int.natCast_dvd.mp hdiff
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · exact hd.trans (dvd_prod_of_mem (fun ab : ℤ × ℤ ↦ (ab.1 - ab.2).natAbs)
      ((mem_pairs A a b).mpr ⟨ha, hb, hlt⟩))
  · have hrev : (b - a).natAbs = (a - b).natAbs := by rw [← neg_sub a b, Int.natAbs_neg]
    have hd' : p ∣ (b - a).natAbs := by rwa [hrev]
    exact hd'.trans (dvd_prod_of_mem (fun ab : ℤ × ℤ ↦ (ab.1 - ab.2).natAbs)
      ((mem_pairs A b a).mpr ⟨hb, ha, hgt⟩))

theorem private_prime_parity (A : Finset ℤ) (n p : ℕ) (a : ℤ) (ha : a ∈ A)
    (hvalues : ∀ b ∈ A, (n : ℤ) + b ≠ 0)
    (hpa : p ∣ ((n : ℤ) + a).natAbs) (hD : ¬p ∣ resultant A) :
    parityVec (product A n) p = parityVec (((n : ℤ) + a).natAbs) p := by
  have hnonzero : ∀ b ∈ A, ((n : ℤ) + b).natAbs ≠ 0 := by
    intro b hb
    exact Int.natAbs_ne_zero.mpr (hvalues b hb)
  have hprod := congrArg (fun v : ℕ →₀ F₂ ↦ v p)
    (parityVec_prod A (fun b ↦ ((n : ℤ) + b).natAbs) hnonzero)
  change parityVec (product A n) p = _ at hprod
  rw [Finset.sum_apply'] at hprod
  rw [hprod]
  apply sum_eq_single a
  · intro b hb hba
    have hnot : ¬p ∣ ((n : ℤ) + b).natAbs := by
      intro hpb
      exact hD (shared_prime_divides_resultant A n p a b ha hb hba.symm hpa hpb)
    simp only [parityVec_apply, Nat.factorization_eq_zero_of_not_dvd hnot, Nat.cast_zero]
  · intro hnot
    exact False.elim (hnot ha)

theorem linear_support_subset (A : Finset ℤ) (n : ℕ) (a : ℤ) (ha : a ∈ A)
    (hvalues : ∀ b ∈ A, (n : ℤ) + b ≠ 0) :
    oddPrimeSupport (((n : ℤ) + a).natAbs) ⊆ (kernel A n * resultant A).primeFactors := by
  intro p hp
  have hprime := prime_of_mem_oddPrimeSupport hp
  have hpa := PaperP1.TruncatedKernelProducts.dvd_of_mem_oddPrimeSupport hp
  have hdiv : p ∣ kernel A n * resultant A := by
    by_cases hD : p ∣ resultant A
    · exact dvd_mul_of_dvd_right hD _
    · have hpar := private_prime_parity A n p a ha hvalues hpa hD
      have hnonzero : parityVec (product A n) p ≠ 0 := by
        rw [hpar]
        exact mem_oddPrimeSupport_iff_parityVec_ne_zero.mp hp
      have hk : p ∣ kernel A n := (prime_dvd_squarefreeKernel_iff (product A n) p hprime).mpr
        (mem_oddPrimeSupport_iff_parityVec_ne_zero.mpr hnonzero)
      exact dvd_mul_of_dvd_left hk _
  exact Nat.mem_primeFactors.mpr ⟨hprime, hdiv, (Nat.mul_pos (kernel_pos A n) (resultant_pos A)).ne'⟩

theorem linear_kernel_divides_radical (A : Finset ℤ) (n : ℕ) (a : ℤ) (ha : a ∈ A)
    (hvalues : ∀ b ∈ A, (n : ℤ) + b ≠ 0) :
    squarefreeKernel (((n : ℤ) + a).natAbs) ∣ (kernel A n * resultant A).primeFactors.prod id := by
  exact prod_dvd_prod_of_subset _ _ id (linear_support_subset A n a ha hvalues)

end PaperP1.SplitOffsetSupports
