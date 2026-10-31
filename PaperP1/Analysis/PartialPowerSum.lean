module

public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

/-! # A finite reciprocal-power sum below the summability threshold -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PartialPowerSum

open Finset Set MeasureTheory

def powerSum (σ : ℝ) (T : ℕ) : ℝ := ∑ k ∈ Finset.Icc 1 T, (k : ℝ) ^ (-σ)

theorem powerSum_nonneg (σ : ℝ) (T : ℕ) : 0 ≤ powerSum σ T := by
  apply sum_nonneg
  intro k _
  exact Real.rpow_nonneg (Nat.cast_nonneg k) _

theorem powerSum_eq_shifted (σ : ℝ) (T : ℕ) :
    powerSum σ T = ∑ i ∈ range T, (i + 1 : ℝ) ^ (-σ) := by
  symm
  apply sum_bij (fun i _ ↦ i + 1)
  · intro i hi
    exact mem_Icc.mpr ⟨by omega, by have := mem_range.mp hi; omega⟩
  · intro i _ j _ hij
    omega
  · intro k hk
    obtain ⟨hk, hkT⟩ := mem_Icc.mp hk
    exact ⟨k - 1, mem_range.mpr (by omega), by omega⟩
  · intro i _
    simp only [Nat.cast_add, Nat.cast_one]

theorem powerSum_le (σ : ℝ) (hσ : 0 ≤ σ) (hσ1 : σ < 1) (T : ℕ) :
    powerSum σ T ≤ (T : ℝ) ^ (1 - σ) / (1 - σ) := by
  have hanti : AntitoneOn (fun x : ℝ ↦ x ^ (-σ)) (Set.Ioc 0 (0 + (T : ℝ))) := by
    intro x hx y _ hxy
    exact Real.rpow_le_rpow_of_nonpos hx.1 hxy (by linarith)
  have hint : IntegrableOn (fun x : ℝ ↦ x ^ (-σ)) (Set.Icc 0 (0 + (T : ℝ))) := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by positivity)).mp
    exact intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have h := hanti.sum_le_integral_of_integrableOn hint
  rw [integral_rpow (Or.inl (by linarith : -1 < -σ))] at h
  simpa only [zero_add, Nat.cast_add, Nat.cast_one,
    show -σ + 1 = 1 - σ by ring,
    Real.zero_rpow (by linarith : 1 - σ ≠ 0), sub_zero,
    ← powerSum_eq_shifted] using h

end PaperP1.PartialPowerSum
