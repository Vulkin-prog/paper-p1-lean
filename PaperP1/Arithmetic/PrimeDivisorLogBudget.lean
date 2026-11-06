module

public import PaperP1.Arithmetic.PrimePowerLogSeparation
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.Algebra.BigOperators.Field

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimeDivisorLogBudget

open Finset

theorem log_sum_le (S : Finset ℕ) (hprimes : ∀ p ∈ S, p.Prime) (z : ℤ)
    (hz : z ≠ 0) (hdiv : ∀ p ∈ S, (p : ℤ) ∣ z) :
    (∑ p ∈ S, Real.log (p : ℝ)) ≤ Real.log (z.natAbs : ℝ) := by
  have hcop : (S : Set ℕ).Pairwise (fun p q ↦ IsCoprime (p : ℤ) (q : ℤ)) := by
    intro p hp q hq hpq
    exact Int.isCoprime_iff_nat_coprime.mpr
      (by simpa using (Nat.coprime_primes (hprimes p hp) (hprimes q hq)).mpr hpq)
  have hd : ((∏ p ∈ S, p : ℕ) : ℤ) ∣ z := by
    simpa only [Nat.cast_prod] using Finset.prod_dvd_of_coprime hcop hdiv
  have hb := Int.natAbs_le_of_dvd_ne_zero hd hz
  simp only [Int.natAbs_natCast] at hb
  have hpos : (0 : ℝ) < (∏ p ∈ S, p : ℕ) := by
    exact_mod_cast Finset.prod_pos (fun p hp ↦ (hprimes p hp).pos)
  have hbR : ((∏ p ∈ S, p : ℕ) : ℝ) ≤ (z.natAbs : ℝ) := by exact_mod_cast hb
  have hlog := Real.log_le_log hpos hbR
  rw [Nat.cast_prod, Real.log_prod] at hlog
  · exact hlog
  · intro p hp
    exact_mod_cast (hprimes p hp).ne_zero

theorem weighted_log_sum_le (S : Finset ℕ) (hprimes : ∀ p ∈ S, p.Prime) (z : ℤ)
    (hz : z ≠ 0) (hdiv : ∀ p ∈ S, (p : ℤ) ∣ z)
    (K : ℝ) (hK : 0 < K) (hlarge : ∀ p ∈ S, K ≤ (p : ℝ)) :
    (∑ p ∈ S, Real.log (p : ℝ) / p) ≤ Real.log (z.natAbs : ℝ) / K := by
  calc
    _ ≤ ∑ p ∈ S, Real.log (p : ℝ) / K := by
      apply Finset.sum_le_sum
      intro p hp
      exact div_le_div_of_nonneg_left (Real.log_natCast_nonneg p) hK (hlarge p hp)
    _ = (∑ p ∈ S, Real.log (p : ℝ)) / K := (Finset.sum_div S _ K).symm
    _ ≤ _ := div_le_div_of_nonneg_right (log_sum_le S hprimes z hz hdiv) hK.le

end PaperP1.PrimeDivisorLogBudget
