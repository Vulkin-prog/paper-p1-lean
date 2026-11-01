module

public import PaperP1.Asymptotics.BoundaryCutoff
public import PaperP1.Asymptotics.ModerateOrderLogarithm

/-! # Admissible growing trials and the actual cutoff's critical range -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BoundaryCutoffTrial

open Filter PaperP1.ModerateOrder PaperP1.ModerateOrderLogarithm PaperP1.BoundaryCutoff

theorem trial_condition_eventually (A Λ : ℝ) (hA : 0 < A) (hΛ : 0 < Λ) (hgap : 3 < 2 / A) :
    ∀ᶠ N : ℕ in atTop, Condition Λ N (order A N) := by
  have hinit := (order_real_tendsto_atTop A hA).eventually
    (eventually_ge_atTop ((max 4 ⌈4 * Real.exp 1 * Λ⌉₊ : ℕ) : ℝ))
  have hcost := (logarithmic_cost_tendsto A (2 * Real.exp 1 * Λ) hA (by positivity)).eventually
    (eventually_gt_nhds hgap)
  filter_upwards [hinit, hcost,
    PaperP1.PrimeLogBudget.log_nat_tendsto_atTop.eventually (eventually_ge_atTop 2)] with N hi hc hH
  have hHpos : 0 < Real.log N := by linarith
  refine ⟨by exact_mod_cast hi, ?_⟩
  have hbudget := (lt_div_iff₀ hHpos).mp hc
  linarith

theorem cutoff_le_trial_eventually (A Λ : ℝ) (hA : 0 < A) (hΛ : 0 < Λ) (hgap : 3 < 2 / A) :
    ∀ᶠ N : ℕ in atTop, cutoff Λ hΛ N ≤ order A N := by
  filter_upwards [trial_condition_eventually A Λ hA hΛ hgap] with N hN
  exact cutoff_minimal Λ hΛ N (order A N) hN

theorem cutoff_div_log_tendsto (Λ : ℝ) (hΛ : 0 < Λ) :
    Tendsto (fun N : ℕ ↦ (cutoff Λ hΛ N : ℝ) / Real.log N) atTop (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (show Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (nhds 0) from tendsto_const_nhds)
    (order_div_log_tendsto_zero (1 / 2 : ℝ) (by norm_num))
  · filter_upwards [PaperP1.PrimeLogBudget.log_nat_tendsto_atTop.eventually (eventually_ge_atTop 2)] with N hH
    exact div_nonneg (Nat.cast_nonneg _) (by linarith)
  · filter_upwards [cutoff_le_trial_eventually (1 / 2 : ℝ) Λ (by norm_num) hΛ (by norm_num),
      PaperP1.PrimeLogBudget.log_nat_tendsto_atTop.eventually (eventually_ge_atTop 2)] with N hK hH
    exact div_le_div_of_nonneg_right (by exact_mod_cast hK) (by linarith)

theorem critical_quarter_range (C Λ : ℝ) (hΛ : 0 < Λ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → cutoff Λ hΛ N ≤ L / 4 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hδ : (0 : ℝ) < 1 / (8 * Real.log 2) := by positivity
  obtain ⟨Ns, hNs⟩ := eventually_atTop.mp
    ((cutoff_div_log_tendsto Λ hΛ).eventually (eventually_lt_nhds hδ))
  obtain ⟨Nh, hNh⟩ := eventually_atTop.mp
    (PaperP1.PrimeLogBudget.log_nat_tendsto_atTop.eventually (eventually_ge_atTop (max 2 (2 * C * Real.log 2))))
  refine ⟨max Ns Nh, ?_⟩
  intro N hN L hband
  have hH := hNh N (by omega)
  have hHpos : 0 < Real.log N := by have := (le_max_left _ _).trans hH; linarith
  have hsmall : (cutoff Λ hΛ N : ℝ) ≤ Real.log N / (8 * Real.log 2) := by
    have h := (div_lt_iff₀ hHpos).mp (hNs N (by omega))
    simpa only [one_div, mul_comm, div_eq_mul_inv, one_mul] using h.le
  have hC : C ≤ Real.log N / (2 * Real.log 2) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * Real.log 2)).mpr
    have h := (le_max_right _ _).trans hH
    nlinarith only [h]
  have hbandlo : Real.log N / Real.log 2 - C ≤ (L : ℝ) := by linarith [(abs_le.mp hband).1]
  have hidentity : Real.log N / Real.log 2 = 2 * (Real.log N / (2 * Real.log 2)) := by field_simp
  have hL : Real.log N / (2 * Real.log 2) ≤ (L : ℝ) := by rw [hidentity] at hbandlo; linarith
  have hfour : 4 * (cutoff Λ hΛ N : ℝ) ≤ (L : ℝ) := by
    calc
      _ ≤ 4 * (Real.log N / (8 * Real.log 2)) := mul_le_mul_of_nonneg_left hsmall (by norm_num)
      _ = Real.log N / (2 * Real.log 2) := by field_simp; norm_num
      _ ≤ _ := hL
  have hnat : 4 * cutoff Λ hΛ N ≤ L := by exact_mod_cast hfour
  omega

end PaperP1.BoundaryCutoffTrial
