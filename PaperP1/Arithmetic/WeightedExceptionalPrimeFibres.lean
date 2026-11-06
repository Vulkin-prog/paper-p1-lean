module

public import PaperP1.Arithmetic.PrimeDivisorLogBudget
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! # Actual exceptional column populations have an explicit weighted prime-loss budget -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.WeightedExceptionalPrimeFibres

open Finset
open scoped Classical

variable {ι : Type*} [Fintype ι]

theorem weighted_loss (S : Finset ℕ) (hprimes : ∀ p ∈ S, p.Prime)
    (B : ℕ → ι → Prop) (z : ι → ℤ) (hz : ∀ j, z j ≠ 0)
    (hdiv : ∀ p ∈ S, ∀ j, B p j → (p : ℤ) ∣ z j)
    (K : ℝ) (hK : 0 < K) (hlarge : ∀ p ∈ S, K ≤ (p : ℝ)) :
    (∑ p ∈ S, (Nat.card {j // B p j} : ℝ) * (Real.log (p : ℝ) / p)) ≤
      (∑ j, Real.log ((z j).natAbs : ℝ)) / K := by
  classical
  have hcount (p : ℕ) : (Nat.card {j // B p j} : ℝ) * (Real.log (p : ℝ) / p) =
      ∑ j, if B p j then Real.log (p : ℝ) / p else 0 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, ← Finset.sum_filter]
    simp
  calc
    _ = ∑ p ∈ S, ∑ j, if B p j then Real.log (p : ℝ) / p else 0 := by
      apply Finset.sum_congr rfl
      intro p _
      exact hcount p
    _ = ∑ j, ∑ p ∈ S, if B p j then Real.log (p : ℝ) / p else 0 := Finset.sum_comm
    _ = ∑ j, ∑ p ∈ S.filter (fun p ↦ B p j), Real.log (p : ℝ) / p := by
      simp only [Finset.sum_filter]
    _ ≤ ∑ j, Real.log ((z j).natAbs : ℝ) / K := by
      apply Finset.sum_le_sum
      intro j _
      apply PrimeDivisorLogBudget.weighted_log_sum_le (S.filter (fun p ↦ B p j))
        (fun p hp ↦ hprimes p (mem_filter.mp hp).1) (z j) (hz j)
        (fun p hp ↦ hdiv p (mem_filter.mp hp).1 j (mem_filter.mp hp).2) K hK
        (fun p hp ↦ hlarge p (mem_filter.mp hp).1)
    _ = _ := (Finset.sum_div univ _ K).symm

theorem uniform_height_loss (S : Finset ℕ) (hprimes : ∀ p ∈ S, p.Prime)
    (B : ℕ → ι → Prop) (z : ι → ℤ) (hz : ∀ j, z j ≠ 0)
    (hdiv : ∀ p ∈ S, ∀ j, B p j → (p : ℤ) ∣ z j)
    (K : ℝ) (hK : 0 < K) (hlarge : ∀ p ∈ S, K ≤ (p : ℝ))
    (A H m : ℕ) (hA : 0 < A) (hH : 1 ≤ H)
    (hbound : ∀ j, (z j).natAbs ≤ A * H ^ m) :
    (∑ p ∈ S, (Nat.card {j // B p j} : ℝ) * (Real.log (p : ℝ) / p)) ≤
      (Fintype.card ι : ℝ) * (Real.log (A : ℝ) + (m : ℝ) * Real.log (H : ℝ)) / K := by
  have hApos : (0 : ℝ) < A := by exact_mod_cast hA
  have hHpos : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hterm (j : ι) : Real.log ((z j).natAbs : ℝ) ≤
      Real.log (A : ℝ) + (m : ℝ) * Real.log (H : ℝ) := by
    have hzpos : (0 : ℝ) < (z j).natAbs := by exact_mod_cast (Int.natAbs_pos.mpr (hz j))
    have hbR : ((z j).natAbs : ℝ) ≤ ((A * H ^ m : ℕ) : ℝ) := by exact_mod_cast hbound j
    have hh := Real.log_le_log hzpos hbR
    rw [Nat.cast_mul, Nat.cast_pow, Real.log_mul hApos.ne' (pow_ne_zero m hHpos.ne'), Real.log_pow] at hh
    exact hh
  have hsum : (∑ j, Real.log ((z j).natAbs : ℝ)) ≤
      (Fintype.card ι : ℝ) * (Real.log (A : ℝ) + (m : ℝ) * Real.log (H : ℝ)) := by
    simpa only [Finset.sum_const, card_univ, nsmul_eq_mul] using
      Finset.sum_le_sum (fun j (_ : j ∈ (univ : Finset ι)) ↦ hterm j)
  exact (weighted_loss S hprimes B z hz hdiv K hK hlarge).trans
    (div_le_div_of_nonneg_right hsum hK.le)

end PaperP1.WeightedExceptionalPrimeFibres
