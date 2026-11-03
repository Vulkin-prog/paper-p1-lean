module

public import PaperP1.Arithmetic.PrimeProductBudget

/-! # Prime assignment budgets for a fixed number of anchor values -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MultiAnchorPrimeBudget

open Finset

def assignmentExponent (t N : ℕ) (Y : ℝ) : ℕ :=
  ⌈(t : ℝ) * Real.log (3 * (N : ℝ)) / Real.log Y⌉₊

theorem card_le_assignmentExponent (P : Finset ℕ) (t N : ℕ) (Y : ℝ) (hY : 1 < Y)
    (hP : ∀ p ∈ P, Nat.Prime p ∧ Y < (p : ℝ))
    (hprod : P.prod id ≤ (3 * N) ^ t) : P.card ≤ assignmentExponent t N Y := by
  have hYpos : 0 < Y := by linarith
  have hQpos : (0 : ℝ) < P.prod id := by
    exact_mod_cast prod_pos (fun p hp ↦ (hP p hp).1.pos)
  have hQupper : (↑(P.prod id) : ℝ) ≤ (3 * (N : ℝ)) ^ t := by exact_mod_cast hprod
  have hlogprod : Real.log (P.prod id : ℕ) = ∑ p ∈ P, Real.log p := by
    rw [Nat.cast_prod]
    exact Real.log_prod (fun p hp ↦ by exact_mod_cast (hP p hp).1.ne_zero)
  have hlow : (P.card : ℝ) * Real.log Y ≤ Real.log (P.prod id : ℕ) := by
    rw [hlogprod]
    calc
      _ = ∑ _p ∈ P, Real.log Y := by simp
      _ ≤ _ := sum_le_sum (fun p hp ↦ Real.log_le_log hYpos (hP p hp).2.le)
  have hupp : Real.log (P.prod id : ℕ) ≤ (t : ℝ) * Real.log (3 * (N : ℝ)) := by
    simpa only [Real.log_pow] using Real.log_le_log hQpos hQupper
  have hratio : (P.card : ℝ) ≤ (t : ℝ) * Real.log (3 * (N : ℝ)) / Real.log Y :=
    (le_div_iff₀ (Real.log_pos hY)).mpr (hlow.trans hupp)
  have hceil : (P.card : ℝ) ≤ assignmentExponent t N Y := hratio.trans (Nat.le_ceil _)
  exact_mod_cast hceil

end PaperP1.MultiAnchorPrimeBudget
