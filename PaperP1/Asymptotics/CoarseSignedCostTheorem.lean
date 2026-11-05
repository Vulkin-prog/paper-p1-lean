module

public import PaperP1.Asymptotics.CoarseSignedCostLower
public import PaperP1.Asymptotics.SignedSaddleCriticalLower
public import PaperP1.Asymptotics.SignedSaddleCostTheorem

/-! # The original specified signed cost has a coarse saddle lower bound internally

The exponent twelve replaces the unproved sharp exponent two only in this
separate weaker theorem. The canonical fine conclusion remains conditional.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CoarseSignedCostTheorem

open Filter SaddleParameters SaddleScales HardSaddleGrowth SignedPrivateDyadicField
  SignedPrivateField SignedSaddleExcess SignedSaddleCostTheorem

theorem uniform_lower_from_width (C D : ℝ) (hD : 0 ≤ D) :
    ∃ N₀ : ℕ, ∀ N : ℕ, ∀ hN : max N₀ 2 ≤ N, ∀ L E : ℕ, ∀ hL : 1 ≤ L,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ((L + E + 2 : ℕ) : ℝ) ≤ D * Real.log N →
      Real.exp (-12 * saddleCutoff 1 (Real.log N)) ≤
        cost (data (E := E) (by omega : 2 ≤ N) hL) := by
  obtain ⟨NC, hc⟩ := CoarseSignedCostLower.uniform_actual_lower D hD
  let c := SignedSaddleCriticalLower.lowerConstant C
  have hcpos : 0 < c := SignedSaddleCriticalLower.lowerConstant_pos C
  have hlogT : Tendsto (fun N : ℕ ↦ Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hvT := tendsto_cutoff_atTop.comp hlogT
  obtain ⟨NV, hv⟩ := eventually_atTop.mp (hvT.eventually (eventually_ge_atTop (-Real.log c)))
  refine ⟨max NC NV, ?_⟩
  intro N hN L E hL hcrit hwidth
  have hcost := hc N (by omega) L E hL hwidth
  have hpref := SignedSaddleCriticalLower.critical_prefactor (by omega : 2 ≤ N) hcrit
  have hfactor := hv N (by omega)
  change -Real.log c ≤ saddleCutoff 1 (Real.log N) at hfactor
  calc
    _ ≤ Real.exp (Real.log c + -11 * saddleCutoff 1 (Real.log N)) :=
      Real.exp_le_exp.mpr (by linarith only [hfactor])
    _ = c * Real.exp (-11 * saddleCutoff 1 (Real.log N)) := by rw [Real.exp_add, Real.exp_log hcpos]
    _ ≤ _ := (mul_le_mul_of_nonneg_right hpref (Real.exp_nonneg _)).trans hcost

theorem uniform_lower (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L : ℕ,
      1 ≤ L → |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        Real.exp (-12 * saddleCutoff 1 (Real.log N)) ≤ specifiedCost N L := by
  obtain ⟨NW, hw⟩ := uniform_width C
  obtain ⟨NC, hc⟩ := uniform_lower_from_width C widthConstant widthConstant_pos.le
  refine ⟨max NW NC, ?_⟩
  intro N hN L hL hcrit
  rw [specifiedCost_eq (by omega : 2 ≤ N) hL]
  exact hc N (by omega) L (excess N) hL hcrit (hw N (by omega) L hcrit)

theorem uniform_log_lower (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L : ℕ,
      1 ≤ L → |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        -12 * saddleCutoff 1 (Real.log N) ≤ Real.log (specifiedCost N L) := by
  obtain ⟨N₀, h⟩ := uniform_lower C
  refine ⟨N₀, ?_⟩
  intro N hN L hL hcrit
  have hh := Real.log_le_log (Real.exp_pos _) (h N hN L hL hcrit)
  simpa only [Real.log_exp] using hh

end PaperP1.CoarseSignedCostTheorem
