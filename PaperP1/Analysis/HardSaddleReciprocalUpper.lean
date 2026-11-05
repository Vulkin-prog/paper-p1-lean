module

public import PaperP1.Analysis.PrimeEulerSaddleScale
public import PaperP1.Analysis.ElementaryReciprocalPivotUpper
public import PaperP1.Analysis.CoarseSaddlePowerErrors

/-! # An internal coarse hard-saddle upper bound for actual pivot reciprocals

The prime harmonic estimate is uniform at a moving exponent approaching one.
It gives the correct hard-saddle order, with an explicit weaker constant.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HardSaddleReciprocalUpper

open Filter SaddleParameters SaddleScales HardSaddleGrowth OddPrimePivot ReciprocalOddPivots

theorem uniform_upper : ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2,
    pivotSum (3 * N) + 1 ≤ (N : ℝ) * Real.exp (-saddleCutoff 1 (Real.log N) / 9) := by
  let C := PrimeHarmonicUpper.constant
  have hC : 0 < C := PrimeHarmonicUpper.constant_pos
  obtain ⟨HB, hb⟩ := square_band_eventually
  have hsmallT := isLittleO_log_rpow_rpow_atTop (1 : ℝ) (by norm_num : (0 : ℝ) < 1 / 4)
  have hevent : ∀ᶠ H : ℝ in atTop,
      max HB 4 ≤ H ∧ 1 ≤ Real.log H ∧ saddleCutoff 1 H / H < 1 ∧
        Real.log H / saddleCutoff 1 H < 1 ∧
        ‖Real.log H ^ (1 : ℝ)‖ ≤ (1 / (24 * C)) * ‖H ^ (1 / 4 : ℝ)‖ ∧
        720 ≤ saddleCutoff 1 H :=
    (eventually_ge_atTop (max HB 4)).and
      ((Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))).and
        ((tendsto_cutoff_div_height.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))).and
          ((tendsto_log_div_cutoff.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))).and
            ((hsmallT.bound (by positivity : 0 < 1 / (24 * C))).and
              (tendsto_cutoff_atTop.eventually (eventually_ge_atTop (720 : ℝ)))))))
  obtain ⟨H₀, hh⟩ := eventually_atTop.mp hevent
  have hlogT : Tendsto (fun N : ℕ ↦ Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hlogT.eventually (eventually_ge_atTop H₀))
  refine ⟨N₀, ?_⟩
  intro N hN
  let H := Real.log (N : ℝ)
  let V := saddleCutoff 1 H
  let δ := Real.log H / (4 * V)
  let σ := 1 - δ
  let Y := ⌊Real.exp V⌋₊
  obtain ⟨hbase, hlog, hvsmall, hlogsmall, hsmall, hVlarge⟩ := hh H (hN₀ N (by omega))
  obtain ⟨hHp, hVp, _hVlower, hVupper⟩ := hb H ((le_max_left _ _).trans hbase)
  have hH4 : 4 ≤ H := (le_max_right _ _).trans hbase
  have hlogp : 0 < Real.log H := by linarith only [hlog]
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hV1 : 1 ≤ V := by linarith only [hVlarge]
  have hVH : V ≤ H := by
    have hx := (div_le_iff₀ hHp).mp hvsmall.le
    exact hx.trans_eq (by ring)
  have hrootV : Real.sqrt H ≤ V := by
    have hs := Real.sq_sqrt hHp.le
    have hz := Real.sqrt_nonneg H
    nlinarith only [hs, hz, hVp, _hVlower]
  have hlogV : Real.log H ≤ V := by
    have hx := (div_le_iff₀ hVp).mp hlogsmall.le
    simpa only [one_mul] using hx
  have hδpos : 0 < δ := by dsimp only [δ]; positivity
  have hδhalf : δ ≤ 1 / 2 := by
    dsimp only [δ]
    apply (div_le_iff₀ (by positivity : 0 < 4 * V)).mpr
    linarith only [hlogV, hVp]
  have hσ : 1 / 2 ≤ σ := by dsimp only [σ]; linarith only [hδhalf]
  have hσ1 : σ ≤ 1 := by dsimp only [σ]; linarith only [hδpos]
  have hDelta : 1 - σ = δ := by dsimp only [σ]; ring
  have hsmall' : Real.log H ≤ (1 / (24 * C)) * H ^ (1 / 4 : ℝ) := by
    simpa only [Real.rpow_one, Real.norm_eq_abs, abs_of_pos hlogp,
      abs_of_nonneg (Real.rpow_nonneg hHp.le (1 / 4))] using hsmall
  have hsmall'' : 24 * C * Real.log H ≤ H ^ (1 / 4 : ℝ) := by
    have hx := mul_le_mul_of_nonneg_left hsmall' (by positivity : 0 ≤ 24 * C)
    have hid : (24 * C) * ((1 / (24 * C)) * H ^ (1 / 4 : ℝ)) = H ^ (1 / 4 : ℝ) := by field_simp
    rw [hid] at hx
    exact hx
  have heV : 2 ≤ Real.exp V := by have hx := Real.add_one_le_exp V; linarith only [hx, hV1]
  have hY : 2 ≤ Y := (Nat.le_floor_iff (Real.exp_nonneg _)).mpr (by simpa only [Nat.cast_ofNat] using heV)
  have hYupper : (Y : ℝ) ≤ Real.exp V := Nat.floor_le (Real.exp_nonneg _)
  have hYhalf : Real.exp V ≤ 2 * (Y : ℝ) := by
    have hx := Nat.lt_floor_add_one (Real.exp V)
    change Real.exp V < (Y : ℝ) + 1 at hx
    linarith only [hx, heV]
  have hEuler := PrimeEulerSaddleScale.exponent_bound C H V hC.le hH4 hlog hV1 hVH hrootV hsmall'' Y hY hYupper
  change C * (Y : ℝ) ^ δ * (1 + Real.log (Real.log ((Y : ℝ) + 2))) ≤ V / 8 at hEuler
  have hLoss : V / 4 ≤ H * δ := by
    dsimp only [δ]
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (by positivity : 0 < 4 * V)).mpr
    nlinarith only [hVupper]
  have hNpow : (N : ℝ) ^ σ ≤ (N : ℝ) * Real.exp (-V / 4) := by
    rw [Real.rpow_def_of_pos hn]
    have hexp : H * σ ≤ H + -V / 4 := by dsimp only [σ]; nlinarith only [hLoss]
    calc
      _ ≤ Real.exp (H + -V / 4) := Real.exp_le_exp.mpr hexp
      _ = _ := by rw [Real.exp_add, Real.exp_log hn]
  have hthree : ((3 * N : ℕ) : ℝ) ^ σ ≤ 3 * (N : ℝ) ^ σ := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hn.le]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_self_of_one_le (by norm_num : (1 : ℝ) ≤ 3) hσ1) (Real.rpow_nonneg hn.le _)
  have hcount : ((pivotValues (3 * N) Y).card : ℝ) ≤ 3 * N * Real.exp (-V / 8) := by
    have hx := PrimeHarmonicUpper.pivot_count_uniform (3 * N) Y hY σ hσ hσ1
    rw [hDelta] at hx
    have he : C = PrimeHarmonicUpper.constant := rfl
    rw [← he] at hx
    calc
      _ ≤ ((3 * N : ℕ) : ℝ) ^ σ *
          Real.exp (C * (Y : ℝ) ^ δ * (1 + Real.log (Real.log ((Y : ℝ) + 2)))) := hx
      _ ≤ (3 * ((N : ℝ) * Real.exp (-V / 4))) * Real.exp (V / 8) :=
        mul_le_mul ((hthree.trans (mul_le_mul_of_nonneg_left hNpow (by norm_num))))
          (Real.exp_le_exp.mpr hEuler) (Real.exp_nonneg _) (by positivity)
      _ = 3 * N * (Real.exp (-V / 4) * Real.exp (V / 8)) := by ring
      _ = _ := by rw [← Real.exp_add]; congr 2; ring
  have hinv : 1 / (Y : ℝ) ≤ 2 * Real.exp (-V) := by
    rw [Real.exp_neg]
    change 1 / (Y : ℝ) ≤ 2 / Real.exp V
    exact (div_le_div_iff₀ (by exact_mod_cast (show 0 < Y by omega) : (0 : ℝ) < Y) (Real.exp_pos _)).mpr
      (by simpa only [one_mul] using hYhalf)
  have htail : ((3 * N : ℕ) : ℝ) / Y ≤ 6 * N * Real.exp (-V / 8) := by
    have hx := mul_le_mul_of_nonneg_left hinv (by positivity : (0 : ℝ) ≤ 3 * N)
    have hy : Real.exp (-V) ≤ Real.exp (-V / 8) := Real.exp_le_exp.mpr (by linarith only [hVp])
    calc
      _ ≤ 6 * N * Real.exp (-V) := by
        push_cast
        simp only [div_eq_mul_inv, one_mul] at hx ⊢
        nlinarith only [hx]
      _ ≤ _ := mul_le_mul_of_nonneg_left hy (by positivity)
  have hone : 1 ≤ (N : ℝ) * Real.exp (-V / 8) := by
    have he : (N : ℝ) * Real.exp (-V / 8) = Real.exp (H + -V / 8) := by rw [Real.exp_add, Real.exp_log hn]
    rw [he]
    exact Real.one_le_exp (by linarith only [hVH, hHp])
  have hfinite := ElementaryReciprocalPivotUpper.finite_cutoff (3 * N) Y (by omega)
  have hsum : pivotSum (3 * N) + 1 ≤ 10 * N * Real.exp (-V / 8) := by
    linarith only [hfinite, hcount, htail, hone]
  have hpref : 10 ≤ Real.exp (V / 72) := by
    have hx := Real.add_one_le_exp (V / 72)
    linarith only [hx, hVlarge]
  calc
    _ ≤ 10 * N * Real.exp (-V / 8) := hsum
    _ ≤ Real.exp (V / 72) * N * Real.exp (-V / 8) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpref hn.le) (Real.exp_nonneg _)
    _ = (N : ℝ) * (Real.exp (V / 72) * Real.exp (-V / 8)) := by ring
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

end PaperP1.HardSaddleReciprocalUpper
