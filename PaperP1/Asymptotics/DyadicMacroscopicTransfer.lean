module

public import PaperP1.Asymptotics.MacroscopicHighRelationMass
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Exact transfer from the dyadic interval to a proved macroscopic domain

Every dyadic root belongs to [ceil(sqrt(2N)),2N) for N>=2. The critical
band changes by exactly one and the fixed factor2 is absorbed explicitly.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DyadicMacroscopicTransfer

open Finset PaperP1.Model PaperP1.MacroscopicIntervalGeometry

theorem dyadic_subset {N : ℕ} (hN : 2 ≤ N) :
    dyadicBlock N ⊆ starts (2 * N) (1 / 2) := by
  intro x hx
  obtain ⟨hxlo, hxhi⟩ := mem_Ico.mp hx
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hroot : ((2 * N : ℕ) : ℝ) ^ (1 / 2 : ℝ) ≤ (N : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    apply Real.sqrt_le_iff.mpr
    constructor
    · exact Nat.cast_nonneg N
    · push_cast
      nlinarith only [hn]
  exact mem_starts_iff.mpr ⟨hroot.trans (by exact_mod_cast hxlo), hxhi⟩

theorem critical_band {N L : ℕ} {C : ℝ} (hN : 0 < N)
    (hcrit : |(L : ℝ) - Real.log N / Real.log 2| ≤ C) :
    |(L : ℝ) - Real.log (2 * N : ℕ) / Real.log 2| ≤ C + 1 := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have htwo : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hlog : Real.log (2 * N : ℕ) / Real.log 2 = Real.log N / Real.log 2 + 1 := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hn]
    field_simp
    ring
  rw [hlog]
  have ht := abs_sub_le ((L : ℝ) - Real.log N / Real.log 2) 0 1
  simp only [sub_zero, zero_sub, abs_neg, abs_one] at ht
  have heq : (L : ℝ) - (Real.log N / Real.log 2 + 1) = ((L : ℝ) - Real.log N / Real.log 2) - 1 := by ring
  rw [heq]
  exact ht.trans (add_le_add hcrit le_rfl)

theorem double_power (p ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ((2 * N : ℕ) : ℝ) ^ p ≤ (N : ℝ) ^ (p + ε) := by
  obtain ⟨N₀, h⟩ := PaperP1.HalfCountSchedule.factor_absorption ((2 : ℝ) ^ p) p ε hε
  refine ⟨N₀, ?_⟩
  intro N hN
  rw [Nat.cast_mul, Nat.cast_ofNat, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg N)]
  exact h N (by omega)

end PaperP1.DyadicMacroscopicTransfer
