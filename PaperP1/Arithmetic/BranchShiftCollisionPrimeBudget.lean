module

public import PaperP1.Arithmetic.BranchShiftReductionCertificate
public import PaperP1.Arithmetic.PrimeDivisorLogBudget
public import PaperP1.Arithmetic.P3BadReductionPrimeBudget

/-! # The actual finite set of characteristic-two or branch-collision primes has an explicit logarithmic budget -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BranchShiftCollisionPrimeBudget

open Finset BranchShiftReductionCertificate
open scoped Classical

def badPrimes (S : Finset ℤ) : Set ℕ :=
  {p | p.Prime ∧ (p = 2 ∨ ¬ Set.InjOn (Int.cast : ℤ → ZMod p) (S : Set ℤ))}

theorem divides_certificate (S : Finset ℤ) {p : ℕ} (hp : p ∈ badPrimes S) :
    (p : ℤ) ∣ certificate S := by
  by_contra hnot
  rcases hp.2 with htwo | hcollision
  · exact prime_ne_two S p hnot htwo
  · exact hcollision (injective_reduction S p hnot)

theorem finite (S : Finset ℤ) : (badPrimes S).Finite := by
  apply ((certificate S).natAbs.primeFactors.finite_toSet).subset
  intro p hp
  exact Nat.mem_primeFactors.mpr ⟨hp.1, Int.natCast_dvd.mp (divides_certificate S hp),
    Int.natAbs_ne_zero.mpr (nonzero S)⟩

theorem log_sum (S : Finset ℤ) (B : Finset ℕ) (hB : ∀ p ∈ B, p ∈ badPrimes S) :
    (∑ p ∈ B, Real.log (p : ℝ)) ≤ Real.log ((certificate S).natAbs : ℝ) :=
  PrimeDivisorLogBudget.log_sum_le B (fun p hp ↦ (hB p hp).1) (certificate S) (nonzero S)
    (fun p hp ↦ divides_certificate S (hB p hp))

theorem weighted_log_sum (S : Finset ℤ) (B : Finset ℕ) (hB : ∀ p ∈ B, p ∈ badPrimes S)
    (K : ℝ) (hK : 0 < K) (hlarge : ∀ p ∈ B, K ≤ (p : ℝ)) :
    (∑ p ∈ B, Real.log (p : ℝ) / p) ≤ Real.log ((certificate S).natAbs : ℝ) / K :=
  PrimeDivisorLogBudget.weighted_log_sum_le B (fun p hp ↦ (hB p hp).1) (certificate S)
    (nonzero S) (fun p hp ↦ divides_certificate S (hB p hp)) K hK hlarge

theorem log_height_bound (S : Finset ℤ) (H : ℕ) (hH : 0 < H)
    (hshift : ∀ a ∈ S, |a| ≤ (H : ℤ)) :
    Real.log ((certificate S).natAbs : ℝ) ≤ Real.log 2 +
      ((S.card * (S.card - 1) : ℕ) : ℝ) * Real.log (2 * (H : ℝ)) := by
  have hh := P3BadReductionPrimeBudget.log_height_bound (certificate S) (nonzero S)
    2 (2 * H) (S.card * (S.card - 1)) (by decide) (by positivity) (natAbs_bound S H hshift)
  simpa only [Nat.cast_ofNat, Nat.cast_mul] using hh

theorem full_log_budget (S : Finset ℤ) (H : ℕ) (hH : 0 < H)
    (hshift : ∀ a ∈ S, |a| ≤ (H : ℤ)) :
    ∃ B : Finset ℕ, (∀ p : ℕ, p ∈ B ↔ p ∈ badPrimes S) ∧
      (∑ p ∈ B, Real.log (p : ℝ)) ≤ Real.log 2 +
        ((S.card * (S.card - 1) : ℕ) : ℝ) * Real.log (2 * (H : ℝ)) ∧
      ∀ K : ℝ, 0 < K →
        (∑ p ∈ B.filter (fun p : ℕ ↦ K ≤ (p : ℝ)), Real.log (p : ℝ) / p) ≤
          (Real.log 2 + ((S.card * (S.card - 1) : ℕ) : ℝ) * Real.log (2 * (H : ℝ))) / K := by
  let hf := finite S
  let B := hf.toFinset
  have hB (p : ℕ) : p ∈ B ↔ p ∈ badPrimes S := hf.mem_toFinset
  have hl := log_height_bound S H hH hshift
  refine ⟨B, hB, (log_sum S B (fun p hp ↦ (hB p).mp hp)).trans hl, ?_⟩
  intro K hK
  have hh := weighted_log_sum S (B.filter (fun p : ℕ ↦ K ≤ (p : ℝ)))
    (fun p hp ↦ (hB p).mp (mem_filter.mp hp).1) K hK (fun _ hp ↦ (mem_filter.mp hp).2)
  exact hh.trans (div_le_div_of_nonneg_right hl hK.le)

end PaperP1.BranchShiftCollisionPrimeBudget
