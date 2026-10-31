module

public import PaperP1.Arithmetic.LargeOddKernel
public import PaperP1.Coding.RungeDefectApplication
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

/-!
# A finite local bound for actual defective integers

The small-prime cutoff H and interval width R are independent. This is a
proved finite precursor to companion T1.3; no asymptotic prime-count estimate
is assumed or claimed here.

Finite enumeration and small-cardinality case handling adapt proof patterns
from PaperC/Coding/IntervalDefectBound.lean, commit
b9fa9ba490f201b408a302a86f1594ee620b228b, blob
dbb7fa8dd13e986eb396d88a883ba011d338752b, Apache-2.0.
-/

namespace PaperP1.LocalDefectBound

open Finset DefectCounting DefectivePredicate

noncomputable def primeCount (H : ℕ) : ℕ :=
  (smallPrimesUpTo H).card

noncomputable def smallPrime (H : ℕ) (i : Fin (primeCount H)) : ℕ :=
  ((smallPrimesUpTo H).equivFin.symm i).val

theorem smallPrime_covers {H p : ℕ} (hp : p.Prime) (hpH : p ≤ H) :
    ∃ i : Fin (primeCount H), smallPrime H i = p := by
  let v : smallPrimesUpTo H := ⟨p, mem_smallPrimesUpTo.mpr ⟨hp, hpH⟩⟩
  exact ⟨(smallPrimesUpTo H).equivFin v, by simp [smallPrime, v]⟩

/-- Actual integers satisfying the intrinsic valuation predicate in the
inclusive interval [U,U+R]. -/
noncomputable def defectsInInterval (H U R : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc U (U + R)).filter (HDefective H)

theorem mem_defectsInInterval {H U R n : ℕ} :
    n ∈ defectsInInterval H U R ↔ U ≤ n ∧ n ≤ U + R ∧ HDefective H n := by
  classical
  simp [defectsInInterval, and_assoc]

theorem mem_defectsInInterval_iff_largeOddKernel {H U R n : ℕ} :
    n ∈ defectsInInterval H U R ↔
      U ≤ n ∧ n ≤ U + R ∧ LargeOddKernel.largeOddKernel H n = 1 := by
  rw [mem_defectsInInterval, LargeOddKernel.largeOddKernel_eq_one_iff]

theorem endpoint_growth_of_log
    {R U t : ℕ} (hR : 1 ≤ R) (hU : 0 < U)
    (hlog : (2 * t : ℝ) * Real.log (64 * (R : ℝ)) < Real.log U) :
    (64 * R) ^ (2 * t) < U := by
  have hp : (0 : ℝ) < (((64 * R) ^ (2 * t) : ℕ) : ℝ) := by positivity
  have hUr : (0 : ℝ) < U := by exact_mod_cast hU
  have hlogs :
      Real.log ((((64 * R) ^ (2 * t) : ℕ) : ℝ)) < Real.log U := by
    simpa only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat, Real.log_pow] using hlog
  exact_mod_cast (Real.log_lt_log_iff hp hUr).mp hlogs

/-- Full finite Runge--code--Hamming bound, including small-cardinality cases.
The arithmetic input is the proved degree-uniform T1.1 bound. -/
theorem card_defectsInInterval_lt
    {H U R t : ℕ} (hR : 1 ≤ R) (hU : 2 * R ≤ U) (ht : 1 ≤ t)
    (hgrowth : (64 * R) ^ (2 * t) < U) :
    (defectsInInterval H U R).card <
      max (primeCount H + 1)
        (2 * t * 2 ^ ((primeCount H + 1) / t + 1)) := by
  classical
  let D := defectsInInterval H U R
  let m := D.card
  let enum : Fin m ≃ D := by simpa only [m] using D.equivFin.symm
  let f : Fin m → ℕ := fun i => (enum i).val
  have hfmem (i : Fin m) : f i ∈ defectsInInterval H U R := (enum i).property
  have hfi (i : Fin m) := mem_defectsInInterval.mp (hfmem i)
  have hf0 (i : Fin m) : f i ≠ 0 := by
    have := (hfi i).1
    omega
  let rep (i : Fin m) : HDefectRepresentation H (f i) :=
    representationOfHDefective (hfi i).2.2 (hf0 i)
  let s : Fin m → ℕ := fun i => (rep i).defectPart
  let a : Fin m → ℕ := fun i => (rep i).squarePart
  have hrep (i : Fin m) : f i = s i * a i ^ 2 := (rep i).value_eq
  have hs (i : Fin m) : s i ≠ 0 :=
    defectPart_ne_zero_of_HDefectRepresentation (rep i)
  have ha (i : Fin m) : a i ≠ 0 := by
    intro hai
    apply hf0 i
    simp only [hrep i, hai, zero_pow (by decide : 2 ≠ 0), mul_zero]
  have hsmall : ∀ i p, Nat.Prime p → p ∣ s i →
      ∃ j : Fin (primeCount H), smallPrime H j = p := by
    intro i p hp hps
    change p ∣ (rep i).support.prod id at hps
    obtain ⟨q, hq, hpq⟩ := (hp.prime.dvd_finsetProd_iff id).mp hps
    have hqsmall := mem_smallPrimesUpTo.mp ((rep i).support_subset hq)
    have hpqeq : p = q := (Nat.prime_dvd_prime_iff_eq hp hqsmall.1).mp hpq
    exact smallPrime_covers hp (hpqeq ▸ hqsmall.2)
  have hinj : Function.Injective f := by
    intro i j hij
    apply enum.injective
    exact Subtype.ext hij
  have hlower (i : Fin m) : U ≤ f i := (hfi i).1
  have hupper (i : Fin m) : f i ≤ U + R := (hfi i).2.1
  change m < _
  by_cases hrows : primeCount H + 1 ≤ m
  · by_cases htm : 2 * t ≤ m
    · exact (RungeDefectApplication.defectCode_length_lt_of_endpoint_growth
        (smallPrime H) f s a hrep hs ha hsmall hinj hlower hupper
        hR hU hgrowth ht htm hrows).trans_le (le_max_right _ _)
    · have hsmall : m < 2 * t := by omega
      have hfactor : 0 < 2 ^ ((primeCount H + 1) / t + 1) := by positivity
      exact (hsmall.trans_le (Nat.le_mul_of_pos_right _ hfactor)).trans_le
        (le_max_right _ _)
  · exact (show m < primeCount H + 1 by omega).trans_le (le_max_left _ _)

/-- Logarithmic condition for the exact finite bound. -/
theorem card_defectsInInterval_lt_of_log
    {H U R t : ℕ} (hR : 1 ≤ R) (hU : 2 * R ≤ U) (ht : 1 ≤ t)
    (hlog : (2 * t : ℝ) * Real.log (64 * (R : ℝ)) < Real.log U) :
    (defectsInInterval H U R).card <
      max (primeCount H + 1)
        (2 * t * 2 ^ ((primeCount H + 1) / t + 1)) := by
  exact card_defectsInInterval_lt hR hU ht
    (endpoint_growth_of_log hR (by omega) hlog)

end PaperP1.LocalDefectBound

