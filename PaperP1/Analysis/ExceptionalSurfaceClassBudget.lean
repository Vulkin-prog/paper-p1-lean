module

public import PaperP1.Analysis.CommonCutoffSurfaceBudget

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ExceptionalSurfaceClassBudget

open Finset

def cutoff (K : ℝ) (s : ℕ) : ℕ := ⌊Real.sqrt (2 * (s : ℝ) / K)⌋₊

theorem class_budget {χ : Type*} [Fintype χ] (n : χ → ℕ) (s b : ℕ)
    (hpop : (∑ c, n c) + b = s) (K : ℝ) (hK : 0 < K)
    (hcard : (Fintype.card χ : ℝ) ≤ K) :
    (2 / 3 : ℝ) * s * Real.sqrt (2 * (s : ℝ) / K) - 3 * s -
        Real.sqrt (2 * (s : ℝ) / K) * b ≤
      ((∑ c, (cutoff K s * n c - (cutoff K s + 2).choose 3) : ℕ) : ℝ) := by
  classical
  let L := cutoff K s
  let B := (L + 2).choose 3
  have hlocal (c : χ) : (L : ℝ) * (n c : ℝ) - (B : ℝ) ≤ (L * n c - B : ℕ) := by
    have hn : L * n c ≤ (L * n c - B) + B := by omega
    have hr : (L : ℝ) * (n c : ℝ) ≤ (L * n c - B : ℕ) + (B : ℝ) := by exact_mod_cast hn
    linarith
  have hs : (L : ℝ) * (∑ c, n c : ℕ) - (Fintype.card χ : ℝ) * (B : ℝ) ≤
      ((∑ c, (L * n c - B) : ℕ) : ℝ) := by
    have hh := Finset.sum_le_sum (fun c (_ : c ∈ (univ : Finset χ)) ↦ hlocal c)
    simpa only [Nat.cast_sum, Finset.sum_sub_distrib, Finset.mul_sum,
      Finset.sum_const, card_univ, nsmul_eq_mul] using hh
  have hpopR : (∑ c, n c : ℕ) + (b : ℝ) = (s : ℝ) := by exact_mod_cast hpop
  have hpopL := congrArg (fun x : ℝ ↦ (L : ℝ) * x) hpopR
  simp only [mul_add] at hpopL
  have hB : (B : ℝ) = (L : ℝ) * ((L : ℝ) + 1) * ((L : ℝ) + 2) / 6 :=
    P3SurfaceDivisorLimits.cast_choose_shifted L
  have hopt : (2 / 3 : ℝ) * s * Real.sqrt (2 * (s : ℝ) / K) - 3 * s ≤
      (L : ℝ) * s - K * (B : ℝ) := by
    rw [hB]
    simpa only [L, cutoff, div_eq_mul_inv, mul_assoc] using
      CommonCutoffSurfaceBudget.real_floor_budget (s : ℝ) K (Nat.cast_nonneg s) hK
  have hLb : (L : ℝ) * b ≤ Real.sqrt (2 * (s : ℝ) / K) * b :=
    mul_le_mul_of_nonneg_right (Nat.floor_le (Real.sqrt_nonneg _)) (Nat.cast_nonneg b)
  have hKB : (Fintype.card χ : ℝ) * (B : ℝ) ≤ K * (B : ℝ) :=
    mul_le_mul_of_nonneg_right hcard (Nat.cast_nonneg B)
  change (2 / 3 : ℝ) * s * Real.sqrt (2 * (s : ℝ) / K) - 3 * s -
    Real.sqrt (2 * (s : ℝ) / K) * b ≤ ((∑ c, (L * n c - B) : ℕ) : ℝ)
  linarith only [hopt, hLb, hKB, hs, hpopL]

end PaperP1.ExceptionalSurfaceClassBudget
