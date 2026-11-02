module

public import PaperP1.Arithmetic.CoverRankPrimeBudget
public import PaperP1.Asymptotics.CriticalWindowGeometry

/-! # The actual small-prime rank cost is uniformly below any fixed fraction of the window -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CoverPrimeSmallCost

open PaperP1.CoverRankPrimeBudget PaperP1.LocalDefectBound

theorem uniform_small_cost (C C₀ η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → L + 1 ≤ H →
      (H : ℝ) ≤ C₀ * (L + 1) →
      (3 * (primeCount H + 2) : ℝ) ≤ η * (L + 1) / 4 := by
  obtain ⟨Bmin, hlog⟩ := ElementaryLogGrowth.log_ge_eventually (4 * constant C₀ / η)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C (max 4 Bmin)
  refine ⟨max 10 NG, by omega, ?_⟩
  intro N hN L H hband hBH hH
  have hwidth := (hg N (by omega) L hband).2.1
  have hBfour : 4 ≤ L + 1 := by omega
  have hLB : 4 * constant C₀ / η ≤ Real.log ((L + 1 : ℕ) : ℝ) := (hlog (L + 1) (by omega)).1
  have hlogpos : 0 < Real.log ((L + 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < L + 1 by omega))
  have hratio : constant C₀ / Real.log ((L + 1 : ℕ) : ℝ) ≤ η / 4 := by
    apply (div_le_iff₀ hlogpos).mpr
    have hh := (div_le_iff₀ hη).mp hLB
    nlinarith only [hh]
  calc
    _ ≤ constant C₀ * ((L + 1 : ℕ) : ℝ) / Real.log ((L + 1 : ℕ) : ℝ) :=
      finite_budget hBfour hBH (by simpa only [Nat.cast_add, Nat.cast_one] using hH)
    _ = (constant C₀ / Real.log ((L + 1 : ℕ) : ℝ)) * ((L + 1 : ℕ) : ℝ) := by ring
    _ ≤ (η / 4) * ((L + 1 : ℕ) : ℝ) := mul_le_mul_of_nonneg_right hratio (Nat.cast_nonneg _)
    _ = _ := by push_cast; ring

end PaperP1.CoverPrimeSmallCost
