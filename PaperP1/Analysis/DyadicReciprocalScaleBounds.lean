module

public import PaperP1.Analysis.OrdinaryReciprocalPrimeInput
public import PaperP1.Arithmetic.DyadicOddPivots
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # Negligible square-root loss and logarithmic dyadic multiplicity -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DyadicReciprocalScaleBounds

open Filter PaperP1.SaddleParameters PaperP1.SaddleScales PaperP1.HardSaddleGrowth
  PaperP1.OrdinaryReciprocalPrimeInput

theorem tendsto_nu_div_height :
    Tendsto (fun H : ℝ ↦ saddleNu 1 H / H) atTop (nhds 0) := by
  have ht := tendsto_cutoff_atTop.inv_tendsto_atTop
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with H hH
  change (saddleCutoff 1 H)⁻¹ = (H / saddleCutoff 1 H) / H
  field_simp

theorem clog_bound {N : ℕ} (hN : 2 ≤ N) :
    ((Nat.clog 2 N + 1 : ℕ) : ℝ) ≤ Real.log N / Real.log 2 + 2 := by
  have hlog : 0 ≤ Real.logb 2 N := Real.logb_nonneg (by norm_num)
    (by exact_mod_cast (show 1 ≤ N by omega))
  have hh := (Nat.ceil_lt_add_one hlog).le
  have hc := Real.natCeil_logb_natCast 2 N
  norm_num only [Nat.cast_ofNat] at hc
  rw [hc] at hh
  push_cast
  unfold Real.logb at hh
  linarith only [hh]

theorem logarithmic_prefactor (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2,
      2 * ((Nat.clog 2 N + 1 : ℕ) : ℝ) ≤ Real.exp (η * saddleNu 1 (Real.log N)) := by
  let C : ℝ := 1 / Real.log 2 + 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC : 0 < C := by dsimp [C]; positivity
  have ht : Tendsto (fun H : ℝ ↦ (Real.log (2 * C) + Real.log H) / saddleNu 1 H) atTop (nhds 0) := by
    have hc := (tendsto_const_nhds (x := Real.log (2 * C))).div_atTop
      (tendsto_saddleNu_atTop (by norm_num : (0 : ℝ) < 1))
    simpa only [add_div, add_zero] using hc.add
      (tendsto_log_div_saddleNu (by norm_num : (0 : ℝ) < 1))
  have hnlog : Tendsto (fun N : ℕ ↦ Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N₀, h⟩ := eventually_atTop.mp
    ((hnlog.eventually (eventually_ge_atTop (max (saddleThreshold 1) 1))).and
      ((ht.comp hnlog).eventually (eventually_lt_nhds hη)))
  refine ⟨N₀, ?_⟩
  intro N hN
  obtain ⟨hdom, he⟩ := h N (by omega)
  have hH1 : 1 ≤ Real.log N := (le_max_right _ _).trans hdom
  have hH : 0 < Real.log N := by linarith
  have hV : 0 < saddleCutoff 1 (Real.log N) := saddleCutoff_pos (by norm_num) (by order)
  have hnu : 0 < saddleNu 1 (Real.log N) := div_pos hH hV
  change (Real.log (2 * C) + Real.log (Real.log N)) / saddleNu 1 (Real.log N) < η at he
  have he' := (div_le_iff₀ hnu).mp he.le
  have hclog := clog_bound (by omega : 2 ≤ N)
  have hclog' : ((Nat.clog 2 N + 1 : ℕ) : ℝ) ≤ C * Real.log N := by
    calc
      _ ≤ Real.log N / Real.log 2 + 2 := hclog
      _ ≤ Real.log N / Real.log 2 + 2 * Real.log N := by linarith only [hH1]
      _ = _ := by dsimp [C]; ring
  calc
    _ ≤ 2 * (C * Real.log N) := mul_le_mul_of_nonneg_left hclog' (by norm_num)
    _ = Real.exp (Real.log (2 * C) + Real.log (Real.log N)) := by
      rw [Real.exp_add, Real.exp_log (by positivity : 0 < 2 * C), Real.exp_log hH]
      ring
    _ ≤ _ := Real.exp_le_exp.mpr he'

theorem small_pivot_negligible (ε : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2,
      2 * (Nat.sqrt N + 1 : ℕ) ≤ (N : ℝ) / 2 *
        Real.exp (-2 * saddleCutoff 1 (Real.log N) - ε * saddleNu 1 (Real.log N)) := by
  have ht : Tendsto (fun H : ℝ ↦
      (2 * saddleCutoff 1 H + ε * saddleNu 1 H + Real.log 8) / H) atTop (nhds 0) := by
    have hc : Tendsto (fun H : ℝ ↦ Real.log 8 / H) atTop (nhds 0) := tendsto_const_nhds.div_atTop tendsto_id
    have hh := ((tendsto_cutoff_div_height.const_mul 2).add (tendsto_nu_div_height.const_mul ε)).add hc
    simpa only [add_div, mul_div_assoc, mul_zero, add_zero] using hh
  have hnlog : Tendsto (fun N : ℕ ↦ Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N₀, h⟩ := eventually_atTop.mp
    ((hnlog.eventually (eventually_gt_atTop (0 : ℝ))).and
      ((ht.comp hnlog).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))))
  refine ⟨N₀, ?_⟩
  intro N hN
  obtain ⟨hH, he⟩ := h N (by omega)
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  change (2 * saddleCutoff 1 (Real.log N) + ε * saddleNu 1 (Real.log N) + Real.log 8) / Real.log N < 1 / 2 at he
  have he' := (div_le_iff₀ hH).mp he.le
  have hroot : (Nat.sqrt N : ℝ) ≤ Real.exp (Real.log N / 2) := by
    have hs : (Nat.sqrt N : ℝ) ^ 2 ≤ N := by exact_mod_cast (Nat.le_sqrt'.mp (le_refl (Nat.sqrt N)))
    have heq : Real.exp (Real.log N / 2) ^ 2 = (N : ℝ) := by
      rw [← Real.exp_nat_mul]
      norm_num only [Nat.cast_ofNat]
      rw [show (2 : ℝ) * (Real.log N / 2) = Real.log N by ring, Real.exp_log hn]
    nlinarith only [hs, heq, Real.exp_pos (Real.log N / 2)]
  have hroot1 : (1 : ℝ) ≤ Real.exp (Real.log N / 2) := Real.one_le_exp (by positivity)
  have heq : 4 * Real.exp (Real.log N / 2) =
      (N : ℝ) / 2 * Real.exp (-Real.log N / 2 + Real.log 8) := by
    rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 8),
      show -Real.log (N : ℝ) / 2 = -(Real.log (N : ℝ) / 2) by ring, Real.exp_neg]
    have heN : (N : ℝ) = Real.exp (Real.log N / 2) ^ 2 := by
      rw [← Real.exp_nat_mul]
      norm_num only [Nat.cast_ofNat]
      rw [show (2 : ℝ) * (Real.log N / 2) = Real.log N by ring, Real.exp_log hn]
    field_simp
    nlinarith only [heN]
  calc
    _ ≤ 4 * Real.exp (Real.log N / 2) := by push_cast; nlinarith only [hroot, hroot1]
    _ = _ := heq
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [he'])) (by positivity)

end PaperP1.DyadicReciprocalScaleBounds
