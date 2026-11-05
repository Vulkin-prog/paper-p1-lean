module

public import PaperP1.Arithmetic.ComponentPrimeBudget
public import PaperP1.Arithmetic.LogarithmicPrimeCount
public import PaperP1.Asymptotics.CriticalWindowGeometry

/-! # All small-prime and parity constraints cost o(L) at every bounded logarithmic width -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BoundedWidthPrimeConstraintCost

open PaperP1.LocalDefectBound

theorem uniform_cost (D : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → H ≤ D * (L + 1) →
      (primeCount (10 * (H + 1)) : ℝ) + 2 ≤ ε * L := by
  obtain ⟨B₀, _hB₀, hp⟩ := ComponentPrimeBudget.prime_constraint_cost_eventually
  obtain ⟨B₁, hb⟩ := ElementaryLogGrowth.log_ge_eventually (48 * ((D + 1 : ℕ) : ℝ) / ε)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C (max B₀ B₁)
  refine ⟨3 + NG, by omega, ?_⟩
  intro N hN L H hband hH
  have hgeom := hg N (by omega) L hband
  have hL : 1 ≤ L := by have hh := hgeom.2.2.1; omega
  have hB₀ : B₀ ≤ L + 1 := (le_max_left _ _).trans hgeom.2.1
  have hB₁ : B₁ ≤ L + 1 := (le_max_right _ _).trans hgeom.2.1
  let B := (D + 1) * (L + 1)
  have hBL : L + 1 ≤ B := by dsimp [B]; nlinarith only [Nat.zero_le D]
  have hHB : H + 1 ≤ B := by dsimp [B]; nlinarith only [hH, Nat.zero_le L]
  have hBpos : (0 : ℝ) < B := by dsimp [B]; positivity
  have hlog : 0 < Real.log ((L + 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < L + 1 by omega))
  have hlogmono : Real.log ((L + 1 : ℕ) : ℝ) ≤ Real.log (B : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast hBL)
  have hprime := hp B (hB₀.trans hBL)
  have hmono : (primeCount (10 * (H + 1)) : ℝ) ≤ primeCount (10 * B) := by
    exact_mod_cast LogarithmicPrimeCount.primeCount_mono (Nat.mul_le_mul_left 10 hHB)
  have hlarge := (div_le_iff₀ hε).mp (hb (L + 1) hB₁).1
  have hcoef : 24 * ((D + 1 : ℕ) : ℝ) / Real.log ((L + 1 : ℕ) : ℝ) ≤ ε / 2 := by
    apply (div_le_iff₀ hlog).mpr
    nlinarith only [hlarge]
  calc
    _ ≤ 24 * B / Real.log (B : ℝ) := by linarith only [hprime, hmono]
    _ ≤ 24 * B / Real.log ((L + 1 : ℕ) : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) hlog hlogmono
    _ = (24 * ((D + 1 : ℕ) : ℝ) / Real.log ((L + 1 : ℕ) : ℝ)) * ((L + 1 : ℕ) : ℝ) := by
      dsimp [B]
      push_cast
      ring
    _ ≤ (ε / 2) * ((L + 1 : ℕ) : ℝ) := mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg _)
    _ ≤ ε * L := by
      have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
      push_cast
      nlinarith only [hLr, hε]

end PaperP1.BoundedWidthPrimeConstraintCost
