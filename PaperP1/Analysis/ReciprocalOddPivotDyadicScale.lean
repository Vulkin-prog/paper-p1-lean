module

public import PaperP1.Analysis.DyadicReciprocalScaleBounds
public import PaperP1.Analysis.ReciprocalOddPivotFullScale

/-! # Both assertions of companion T19.15 from the ordinary classical input -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ReciprocalOddPivotDyadicScale

open Filter PaperP1.SaddleParameters PaperP1.SaddleScales PaperP1.ReciprocalOddPivots
  PaperP1.DyadicOddPivots PaperP1.OrdinaryReciprocalPrimeInput
  PaperP1.DyadicReciprocalScaleBounds PaperP1.ReciprocalOddPivotFullScale

theorem nu_shift_bound {H c : ℝ} (hroot : saddleThreshold 1 ≤ H) (hH : 0 < H)
    (hc : 0 ≤ c) (hcH : c ≤ H) :
    saddleNu 1 (H + c) ≤ 2 * saddleNu 1 H := by
  have hv := saddleCutoff_pos (by norm_num : (0 : ℝ) < 1) hroot
  have hmono := PaperP1.SaddleMonotonicity.cutoff_monotone
    (by norm_num : (0 : ℝ) < 1) hroot (by linarith : H ≤ H + c)
  unfold saddleNu
  calc
    _ ≤ (H + c) / saddleCutoff 1 H := div_le_div_of_nonneg_left (by linarith) hv hmono
    _ ≤ (2 * H) / saddleCutoff 1 H := div_le_div_of_nonneg_right (by linarith only [hcH]) hv.le
    _ = _ := by ring

theorem uniform_dyadic_sandwich (hinput : EIPInput) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2,
      (N : ℝ) * Real.exp (-2 * saddleCutoff 1 (Real.log N) - ε * saddleNu 1 (Real.log N)) ≤ dyadicSum N ∧
      dyadicSum N ≤ (N : ℝ) * Real.exp (-2 * saddleCutoff 1 (Real.log N) + ε * saddleNu 1 (Real.log N)) := by
  obtain ⟨NF, hF⟩ := uniform_full_sandwich hinput (ε / 3) (by positivity)
  obtain ⟨NU, hU⟩ := uniform_full_sandwich hinput (ε / 4) (by positivity)
  obtain ⟨NK, hK⟩ := logarithmic_prefactor (ε / 2) (by positivity)
  obtain ⟨NS, hS⟩ := small_pivot_negligible (ε / 3)
  have hnlog : Tendsto (fun N : ℕ ↦ Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨NG, hG⟩ := eventually_atTop.mp
    (hnlog.eventually (eventually_ge_atTop (max (saddleThreshold 1) (max (Real.log 2) 1))))
  refine ⟨max NF (max NU (max NK (max NS NG))), ?_⟩
  intro N hN
  have hn : 0 < N := by omega
  have hnr : (0 : ℝ) < N := by exact_mod_cast hn
  have hdom := hG N (by omega)
  have hH : 0 < Real.log N := by have := (le_max_right _ _).trans ((le_max_right _ _).trans hdom); linarith
  have hroot : saddleThreshold 1 ≤ Real.log N := (le_max_left _ _).trans hdom
  have hv : 0 < saddleCutoff 1 (Real.log N) := saddleCutoff_pos (by norm_num) hroot
  have hnu : 0 ≤ saddleNu 1 (Real.log N) := (div_pos hH hv).le
  have hεν : 0 ≤ ε * saddleNu 1 (Real.log N) := mul_nonneg hε.le hnu
  have hpref := hK N (by omega)
  let K : ℝ := ((Nat.clog 2 N + 1 : ℕ) : ℝ)
  have hKpos : 0 < K := by dsimp [K]; positivity
  have hK1 : 1 ≤ K := by dsimp [K]; exact_mod_cast (show 1 ≤ Nat.clog 2 N + 1 by omega)
  have htwo : 2 ≤ Real.exp ((ε / 2) * saddleNu 1 (Real.log N)) := by
    change 2 * K ≤ Real.exp ((ε / 2) * saddleNu 1 (Real.log N)) at hpref
    linarith only [hpref, hK1]
  have hdouble : Real.log ((2 * N : ℕ) : ℝ) = Real.log N + Real.log 2 := by
    push_cast
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hnr.ne']
    ring
  constructor
  · let B := (N : ℝ) * Real.exp (-2 * saddleCutoff 1 (Real.log N) - ε * saddleNu 1 (Real.log N))
    have hb : 0 ≤ B := by dsimp [B]; positivity
    have hKB : K * B ≤ (N : ℝ) / 2 *
        Real.exp (-2 * saddleCutoff 1 (Real.log N) - (ε / 3) * saddleNu 1 (Real.log N)) := by
      have hk' : K ≤ Real.exp ((ε / 2) * saddleNu 1 (Real.log N)) / 2 := by linarith only [hpref]
      calc
        _ ≤ (Real.exp ((ε / 2) * saddleNu 1 (Real.log N)) / 2) * B := mul_le_mul_of_nonneg_right hk' hb
        _ = (N : ℝ) / 2 * Real.exp (-2 * saddleCutoff 1 (Real.log N) - (ε / 2) * saddleNu 1 (Real.log N)) := by
          have he : -2 * saddleCutoff 1 (Real.log N) - (ε / 2) * saddleNu 1 (Real.log N) =
              (ε / 2) * saddleNu 1 (Real.log N) + (-2 * saddleCutoff 1 (Real.log N) - ε * saddleNu 1 (Real.log N)) := by ring
          rw [he, Real.exp_add]
          dsimp [B]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hεν])) (by positivity)
    have hfinite := full_dyadic_lower_transfer N hn
    have hsmall := hS N (by omega)
    push_cast at hsmall
    have hlower := (hF N (by omega)).1
    have hKD : K * B ≤ K * dyadicSum N := by
      change pivotSum N ≤ 2 * (Nat.sqrt N + 1) + K * dyadicSum N at hfinite
      linarith only [hfinite, hsmall, hlower, hKB]
    change B ≤ dyadicSum N
    by_contra hc
    have hh := mul_pos hKpos (sub_pos.mpr (lt_of_not_ge hc))
    nlinarith only [hh, hKD]
  · have hupper := (hU (2 * N) (by omega)).2
    have hmono := PaperP1.SaddleMonotonicity.cutoff_monotone
      (by norm_num : (0 : ℝ) < 1) hroot (by have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2); linarith : Real.log N ≤ Real.log N + Real.log 2)
    have hnu2 := nu_shift_bound hroot hH (Real.log_nonneg (by norm_num)) (by order : Real.log 2 ≤ Real.log N)
    rw [hdouble] at hupper
    have hexp : -2 * saddleCutoff 1 (Real.log N + Real.log 2) +
        (ε / 4) * saddleNu 1 (Real.log N + Real.log 2) ≤
        -2 * saddleCutoff 1 (Real.log N) + (ε / 2) * saddleNu 1 (Real.log N) := by
      have hh := mul_le_mul_of_nonneg_left hnu2 (by positivity : 0 ≤ ε / 4)
      linarith only [hmono, hh]
    calc
      _ ≤ pivotSum (2 * N) := dyadic_upper_transfer N hn
      _ ≤ (2 * N : ℕ) * Real.exp (-2 * saddleCutoff 1 (Real.log N + Real.log 2) +
          (ε / 4) * saddleNu 1 (Real.log N + Real.log 2)) := hupper
      _ ≤ (2 * N : ℕ) * Real.exp (-2 * saddleCutoff 1 (Real.log N) + (ε / 2) * saddleNu 1 (Real.log N)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity)
      _ ≤ Real.exp ((ε / 2) * saddleNu 1 (Real.log N)) * N *
          Real.exp (-2 * saddleCutoff 1 (Real.log N) + (ε / 2) * saddleNu 1 (Real.log N)) := by
        push_cast
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right htwo hnr.le) (Real.exp_pos _).le
      _ = _ := by
        have he : -2 * saddleCutoff 1 (Real.log N) + ε * saddleNu 1 (Real.log N) =
            (ε / 2) * saddleNu 1 (Real.log N) + (-2 * saddleCutoff 1 (Real.log N) + (ε / 2) * saddleNu 1 (Real.log N)) := by ring
        rw [he, Real.exp_add ((ε / 2) * saddleNu 1 (Real.log N))
          (-2 * saddleCutoff 1 (Real.log N) + (ε / 2) * saddleNu 1 (Real.log N))]
        ring

theorem companion_T19_15 (hinput : EIPInput) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2,
      ((N : ℝ) * Real.exp (-2 * saddleCutoff 1 (Real.log N) - ε * saddleNu 1 (Real.log N)) ≤ pivotSum N ∧
        pivotSum N ≤ (N : ℝ) * Real.exp (-2 * saddleCutoff 1 (Real.log N) + ε * saddleNu 1 (Real.log N))) ∧
      ((N : ℝ) * Real.exp (-2 * saddleCutoff 1 (Real.log N) - ε * saddleNu 1 (Real.log N)) ≤ dyadicSum N ∧
        dyadicSum N ≤ (N : ℝ) * Real.exp (-2 * saddleCutoff 1 (Real.log N) + ε * saddleNu 1 (Real.log N))) := by
  obtain ⟨NF, hF⟩ := uniform_full_sandwich hinput ε hε
  obtain ⟨ND, hD⟩ := uniform_dyadic_sandwich hinput ε hε
  exact ⟨max NF ND, fun N hN ↦ ⟨hF N (by omega), hD N (by omega)⟩⟩

end PaperP1.ReciprocalOddPivotDyadicScale
