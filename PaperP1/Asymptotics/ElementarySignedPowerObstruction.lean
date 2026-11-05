module

public import PaperP1.Asymptotics.ElementarySignedCostLower
public import PaperP1.Asymptotics.SignedSaddleCostTheorem

/-! # The prescribed signed cost has no polynomial decay, without EIP

This proves the power-obstruction clause of T19.16 internally. Its sharp
logarithmic equivalent and two saddle bounds still require the ordinary input.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ElementarySignedPowerObstruction

open Filter SignedPrivateDyadicField SignedSaddleExcess SignedExactWords
  SignedSaddleCostTheorem

theorem uniform_power_obstruction (C α K : ℝ) (hα : 0 < α) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L : ℕ,
      1 ≤ L → |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        K * (N : ℝ) ^ (-α) ≤ specifiedCost N L := by
  let δ := min (α / 2) (1 / 80)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδsmall : δ < 1 / 20 := (min_le_right _ _).trans_lt (by norm_num)
  have hδα : δ < α := (min_le_left _ _).trans_lt (by linarith only [hα])
  obtain ⟨NC, hc⟩ := ElementarySignedCostLower.uniform_actual_lower widthConstant widthConstant_pos.le δ hδ hδsmall
  obtain ⟨NW, hw⟩ := uniform_width C
  let c := SignedSaddleCriticalLower.lowerConstant C
  have hcpos : 0 < c := SignedSaddleCriticalLower.lowerConstant_pos C
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption (K / c) (-α) (α - δ) (by linarith only [hδα])
  refine ⟨max NC (max NW NA), ?_⟩
  intro N hN L hL hcrit
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcost := hc N (by omega) L (excess N) hL (hw N (by omega) L hcrit)
  have hpref := SignedSaddleCriticalLower.critical_prefactor (by omega : 2 ≤ N) hcrit
  have hminor : c * (N : ℝ) ^ (-δ) ≤ specifiedCost N L := by
    rw [specifiedCost_eq (by omega : 2 ≤ N) hL]
    exact (mul_le_mul_of_nonneg_right hpref (Real.rpow_nonneg hn.le _)).trans hcost
  have hpower := ha N (by omega)
  rw [show -α + (α - δ) = -δ by ring] at hpower
  have hh := mul_le_mul_of_nonneg_left hpower hcpos.le
  have hid : c * (K / c * (N : ℝ) ^ (-α)) = K * (N : ℝ) ^ (-α) := by field_simp
  rw [hid] at hh
  exact hh.trans hminor

theorem not_bigO_critical_sequence (C : ℝ) (length : ℕ → ℕ)
    (hseq : ∀ᶠ N : ℕ in atTop, 1 ≤ length N ∧
      |(length N : ℝ) - Real.log N / Real.log 2| ≤ C) (α : ℝ) (hα : 0 < α) :
    ¬ Asymptotics.IsBigO atTop (fun N ↦ specifiedCost N (length N)) (fun N ↦ (N : ℝ) ^ (-α)) := by
  intro h
  obtain ⟨K, hbound⟩ := h.bound
  have hK : 0 < |K| + 1 := by have := abs_nonneg K; linarith
  obtain ⟨N₀, hLower⟩ := uniform_power_obstruction C α (|K| + 1) hα
  have hfalse : ∀ᶠ N : ℕ in atTop, False := by
    filter_upwards [hseq, hbound, eventually_ge_atTop (max N₀ 2)] with N hs hb hN
    have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hp : 0 < (N : ℝ) ^ (-α) := Real.rpow_pos_of_pos hn _
    have hl := hLower N hN (length N) hs.1 hs.2
    have hc : 0 ≤ specifiedCost N (length N) := (mul_pos hK hp).le.trans hl
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hc, abs_of_pos hp] at hb
    have hh := mul_le_mul_of_nonneg_right (le_abs_self K) hp.le
    nlinarith only [hl, hb, hh, hp]
  obtain ⟨_, h⟩ := hfalse.exists
  exact h

end PaperP1.ElementarySignedPowerObstruction
