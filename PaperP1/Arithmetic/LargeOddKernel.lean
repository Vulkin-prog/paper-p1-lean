module

public import PaperP1.Arithmetic.DefectivePredicate

@[expose] public section

/-! # The large odd-prime kernel and the intrinsic defect predicate -/

namespace PaperP1.LargeOddKernel

open Finset Arithmetic DefectivePredicate

/-- Product of the primes above H occurring to odd exponent in n. -/
noncomputable def largeOddKernel (H n : ℕ) : ℕ :=
  ((oddPrimeSupport n).filter (H < ·)).prod id

theorem mem_oddPrimeSupport_iff_parityVec_ne_zero {n p : ℕ} :
    p ∈ oddPrimeSupport n ↔ parityVec n p ≠ 0 := by
  simp only [oddPrimeSupport, Finsupp.mem_support_iff, oddFactorization,
    Finsupp.mapRange_apply, parityVec_apply, ne_eq, ZMod.natCast_eq_zero_iff,
    Nat.dvd_iff_mod_eq_zero]

theorem prime_of_mem_oddPrimeSupport {n p : ℕ} (hp : p ∈ oddPrimeSupport n) :
    p.Prime := by
  have hs : p ∈ n.factorization.support := Finsupp.support_mapRange hp
  exact Nat.prime_of_mem_primeFactors hs

/-- Exact dictionary for the manuscript notation K_H(n)=1. -/
theorem largeOddKernel_eq_one_iff (H n : ℕ) :
    largeOddKernel H n = 1 ↔ HDefective H n := by
  classical
  constructor
  · intro hK p hp hHp
    by_contra hparity
    have hsupport : p ∈ oddPrimeSupport n :=
      mem_oddPrimeSupport_iff_parityVec_ne_zero.mpr hparity
    have hmem : p ∈ (oddPrimeSupport n).filter (H < ·) := mem_filter.mpr ⟨hsupport, hHp⟩
    have hdvd : p ∣ largeOddKernel H n := Finset.dvd_prod_of_mem id hmem
    exact hp.not_dvd_one (by simpa only [hK] using hdvd)
  · intro h
    have hempty : (oddPrimeSupport n).filter (H < ·) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      obtain ⟨hsupport, hHp⟩ := mem_filter.mp hp
      exact (mem_oddPrimeSupport_iff_parityVec_ne_zero.mp hsupport)
        (h p (prime_of_mem_oddPrimeSupport hsupport) hHp)
    simp only [largeOddKernel, hempty, prod_empty]

end PaperP1.LargeOddKernel

