module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! # A literal prime-independent threshold absorbs square-root and linear point-count errors -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SquareRootPointErrorThreshold

theorem exists_threshold (C E η : ℝ) (hC : 0 ≤ C) (hE : 0 ≤ E) (hη : 0 < η) :
    ∃ K : ℕ, ∀ p : ℕ, K ≤ p →
      C * (p : ℝ) * Real.sqrt p + E * p ≤ η * (p : ℝ) ^ 2 := by
  let R : ℝ := 1 + (2 * C / η) ^ 2 + 2 * E / η
  refine ⟨⌈R⌉₊, ?_⟩
  intro p hp
  have hRp : R ≤ (p : ℝ) := (Nat.le_ceil R).trans (by exact_mod_cast hp)
  have hEn : 0 ≤ 2 * E / η := div_nonneg (by positivity) hη.le
  have hCn : 0 ≤ 2 * C / η := div_nonneg (by positivity) hη.le
  have hp1 : (1 : ℝ) ≤ p := by dsimp only [R] at hRp; nlinarith [sq_nonneg (2 * C / η)]
  have hp0 : (0 : ℝ) ≤ p := by linarith
  have hsq : (2 * C / η) ^ 2 ≤ (p : ℝ) := by dsimp only [R] at hRp; linarith
  have hEl : 2 * E / η ≤ (p : ℝ) := by dsimp only [R] at hRp; nlinarith [sq_nonneg (2 * C / η)]
  have hs : 2 * C / η ≤ Real.sqrt p :=
    (Real.sqrt_sq hCn).symm.trans_le (Real.sqrt_le_sqrt hsq)
  have hCl : C ≤ η / 2 * Real.sqrt p := by
    have hh := (div_le_iff₀ hη).mp hs
    nlinarith
  have hEc : E ≤ η / 2 * (p : ℝ) := by
    have hh := (div_le_iff₀ hη).mp hEl
    nlinarith
  have hCs : C * Real.sqrt p ≤ η / 2 * (p : ℝ) := by
    calc
      _ ≤ (η / 2 * Real.sqrt p) * Real.sqrt p :=
        mul_le_mul_of_nonneg_right hCl (Real.sqrt_nonneg _)
      _ = _ := by rw [mul_assoc, ← pow_two, Real.sq_sqrt hp0]
  calc
    _ = (C * Real.sqrt p) * p + E * p := by ring
    _ ≤ (η / 2 * (p : ℝ)) * p + (η / 2 * (p : ℝ)) * p :=
      add_le_add (mul_le_mul_of_nonneg_right hCs hp0) (mul_le_mul_of_nonneg_right hEc hp0)
    _ = η * (p : ℝ) ^ 2 := by ring

end PaperP1.SquareRootPointErrorThreshold
