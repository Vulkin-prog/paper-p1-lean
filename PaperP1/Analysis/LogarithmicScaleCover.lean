module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Data.Finset.Range
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

/-! # A fixed finite cover of logarithmic pivot scales

The number of bands is chosen before the integer scale. Endpoints are
retained, including a pivot equal to one or to the last upper cutoff.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LogarithmicScaleCover

open Finset

theorem interval_cover (K : ℕ) (hK : 1 ≤ K) (u : ℝ) (hu : 0 ≤ u) (hu3 : u ≤ 3) :
    ∃ j ∈ range (3 * K), (j : ℝ) / K ≤ u ∧ u ≤ ((j + 1 : ℕ) : ℝ) / K := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hfloor : (⌊(K : ℝ) * u⌋₊ : ℝ) ≤ (K : ℝ) * u := Nat.floor_le (by positivity)
  by_cases hj : ⌊(K : ℝ) * u⌋₊ < 3 * K
  · refine ⟨⌊(K : ℝ) * u⌋₊, mem_range.mpr hj, ?_, ?_⟩
    · exact (div_le_iff₀ hKpos).mpr (by nlinarith only [hfloor])
    · have hh := Nat.lt_floor_add_one ((K : ℝ) * u)
      apply (le_div_iff₀ hKpos).mpr
      push_cast
      nlinarith only [hh]
  · have hlo : 3 * K ≤ ⌊(K : ℝ) * u⌋₊ := by omega
    have hloR : 3 * (K : ℝ) ≤ (⌊(K : ℝ) * u⌋₊ : ℝ) := by exact_mod_cast hlo
    have hu' : 3 ≤ u := by nlinarith only [hloR, hfloor, hKpos]
    have heq : u = 3 := le_antisymm hu3 hu'
    refine ⟨3 * K - 1, mem_range.mpr (by omega), ?_, ?_⟩
    · rw [heq]
      apply (div_le_iff₀ hKpos).mpr
      have hh : ((3 * K - 1 : ℕ) : ℝ) ≤ ((3 * K : ℕ) : ℝ) := by exact_mod_cast Nat.sub_le (3 * K) 1
      push_cast at hh
      nlinarith only [hh]
    · rw [heq, show 3 * K - 1 + 1 = 3 * K by omega]
      push_cast
      exact (le_div_iff₀ hKpos).mpr (by nlinarith)

theorem exponential_cover (K : ℕ) (hK : 1 ≤ K) (V p : ℝ) (hV : 0 < V)
    (hp : 1 ≤ p) (hu : p ≤ Real.exp (3 * V)) :
    ∃ j ∈ range (3 * K), Real.exp ((j : ℝ) / K * V) ≤ p ∧
      p ≤ Real.exp (((j + 1 : ℕ) : ℝ) / K * V) := by
  have hp0 : 0 < p := by linarith only [hp]
  have hlogp := Real.log_nonneg hp
  have hupper := Real.log_le_log hp0 hu
  rw [Real.log_exp] at hupper
  obtain ⟨j, hj, hl, hh⟩ := interval_cover K hK (Real.log p / V) (by positivity)
    ((div_le_iff₀ hV).mpr hupper)
  refine ⟨j, hj, ?_, ?_⟩
  · calc
      _ ≤ Real.exp (Real.log p) := Real.exp_le_exp.mpr ((le_div_iff₀ hV).mp hl)
      _ = _ := Real.exp_log hp0
  · calc
      _ = Real.exp (Real.log p) := (Real.exp_log hp0).symm
      _ ≤ _ := Real.exp_le_exp.mpr ((div_le_iff₀ hV).mp hh)

end PaperP1.LogarithmicScaleCover
