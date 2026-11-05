module

public import PaperP1.Arithmetic.LogarithmicDegreePrimeScale

/-! # A cubic degree scale for a redundant prime pool -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RedundantDegreePrimeScale

open DegreeUniformAffineParameters

theorem exists_scale (P₀ : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ D N : ℕ, 2 ≤ D → D ≤ N →
      ∃ P : ℕ, P₀ ≤ P ∧
        (avoidanceCount D N : ℝ) * Real.log P ≤ P ∧
        3 * Real.exp 1 * (((D + 1) * N : ℕ) : ℝ) ^ (1 / (D : ℝ)) ≤ P ∧
        (P : ℝ) ≤ K * (D : ℝ) ^ 3 * (logarithmicBudget N : ℝ) ^ 2 *
          (N : ℝ) ^ (1 / (D : ℝ)) := by
  obtain ⟨K, hK, hscale⟩ := LogarithmicDegreePrimeScale.exists_scale (max 16 P₀)
  refine ⟨4 * K, by positivity, ?_⟩
  intro D N hD hDN
  obtain ⟨Q, hQ, hm, hprime, hupper⟩ := hscale D N hD hDN
  have hQ16 : 16 ≤ Q := (le_max_left _ _).trans hQ
  have hQP : P₀ ≤ 4 * Q := by have hp := (le_max_right _ _).trans hQ; omega
  have hlog : Real.log 4 ≤ Real.log (Q : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (show 4 ≤ Q by omega))
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hQPReal : (Q : ℝ) ≤ ((4 * Q : ℕ) : ℝ) := by push_cast; linarith only [hQpos]
  refine ⟨4 * Q, hQP, ?_, hprime.trans hQPReal, ?_⟩
  · have hlogs : Real.log ((4 * Q : ℕ) : ℝ) ≤ 2 * Real.log (Q : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hQpos.ne']
      linarith only [hlog]
    have hh := mul_le_mul_of_nonneg_left hlogs
      (Nat.cast_nonneg (α := ℝ) (avoidanceCount D N))
    push_cast at hh ⊢
    nlinarith only [hh, hm]
  · push_cast
    have hh := mul_le_mul_of_nonneg_left hupper (by norm_num : (0 : ℝ) ≤ 4)
    nlinarith only [hh]

end PaperP1.RedundantDegreePrimeScale
