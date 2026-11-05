module

public import PaperP1.Algebra.GradedHilbertHyperplane

/-! # A positive affine integer-valued tail has an actual positive integer slope -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IntegerLinearHilbertSlope

theorem slope_and_increment (h : ℕ → ℕ) (a b : ℚ) (ha : 0 < a)
    (N : ℕ) (hh : ∀ n ≥ N, a * (n : ℚ) + b = (h n : ℚ)) :
    ∃ d : ℕ, 0 < d ∧ (d : ℚ) = a ∧ ∀ n ≥ N, h (n + 1) = h n + d := by
  have h₀ := hh N le_rfl
  have h₁ := hh (N + 1) (by omega)
  have hdiff : (h (N + 1) : ℚ) - (h N : ℚ) = a := by
    push_cast at h₁
    linarith only [h₀, h₁]
  have hlt : h N < h (N + 1) := by
    exact_mod_cast (show (h N : ℚ) < (h (N + 1) : ℚ) by linarith only [hdiff, ha])
  let d := h (N + 1) - h N
  have hd : (d : ℚ) = a := by
    dsimp [d]
    rw [Nat.cast_sub hlt.le]
    exact hdiff
  refine ⟨d, by dsimp [d]; omega, hd, ?_⟩
  intro n hn
  have hn₀ := hh n hn
  have hn₁ := hh (n + 1) (by omega)
  have heq : (h (n + 1) : ℚ) = (h n : ℚ) + (d : ℚ) := by
    push_cast at hn₁
    linarith only [hn₀, hn₁, hd]
  exact_mod_cast heq

end PaperP1.IntegerLinearHilbertSlope
