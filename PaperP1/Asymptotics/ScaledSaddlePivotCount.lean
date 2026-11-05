module

public import PaperP1.Analysis.ScaledPrimeEulerBound

/-! # Actual small-pivot populations at every fixed multiple of the hard saddle

The loss can be any fixed b below 1/a at cutoff exp(aV_N). The threshold
precedes the actual prime cutoff and all retained integer populations.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ScaledSaddlePivotCount

open Filter SaddleParameters SaddleScales HardSaddleGrowth OddPrimePivot

theorem uniform_count (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : b < 1 / a) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ Y : ℕ, 2 ≤ Y →
      (Y : ℝ) ≤ Real.exp (a * saddleCutoff 1 (Real.log N)) →
        ((pivotValues (3 * N) Y).card : ℝ) ≤ (N : ℝ) * Real.exp (-b * saddleCutoff 1 (Real.log N)) := by
  let r := (1 + a * b) / 2
  have hab' : a * b < 1 := by have hh := (lt_div_iff₀ ha).mp hab; nlinarith only [hh]
  have hr : 0 < r := by dsimp only [r]; positivity
  have hr1 : r < 1 := by dsimp only [r]; linarith only [hab']
  have hbr : b < r / a := by
    apply (lt_div_iff₀ ha).mpr
    dsimp only [r]
    nlinarith only [hab']
  let b₁ := (b + r / a) / 2
  let g := (b₁ - b) / 2
  have hbb : b < b₁ := by dsimp only [b₁]; linarith only [hbr]
  have hbr' : b₁ < r / a := by dsimp only [b₁]; linarith only [hbr]
  have hg : 0 < g := by dsimp only [g]; linarith only [hbb]
  obtain ⟨HE, he⟩ := ScaledPrimeEulerBound.eventual_exponent_bound a r g ha hr.le hr1 hg
  obtain ⟨HB, hbnd⟩ := square_band_eventually
  have hInv : Tendsto (fun H : ℝ ↦ H * Real.log H / (saddleCutoff 1 H) ^ 2) atTop (nhds 2) := by
    have hh := (tendsto_saddleCutoff_square_normalized (by norm_num : (0 : ℝ) < 1)).inv₀
      (by norm_num : (1 : ℝ) / 2 ≠ 0)
    simpa only [inv_div, one_div, inv_inv] using hh
  have hLoss : Tendsto (fun H : ℝ ↦ (r / (2 * a)) * (H * Real.log H / (saddleCutoff 1 H) ^ 2))
      atTop (nhds (r / a)) := by
    have hh := hInv.const_mul (r / (2 * a))
    have hid : r / (2 * a) * 2 = r / a := by ring
    simpa only [hid] using hh
  have hδ : Tendsto (fun H : ℝ ↦ (r / (2 * a)) * (Real.log H / saddleCutoff 1 H)) atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_log_div_cutoff.const_mul (r / (2 * a))
  have hevent : ∀ᶠ H : ℝ in atTop,
      max HE (max HB 4) ≤ H ∧ 1 ≤ Real.log H ∧
        (r / (2 * a)) * (Real.log H / saddleCutoff 1 H) < 1 / 2 ∧
        b₁ < (r / (2 * a)) * (H * Real.log H / (saddleCutoff 1 H) ^ 2) ∧
        Real.log 3 / g ≤ saddleCutoff 1 H :=
    (eventually_ge_atTop (max HE (max HB 4))).and
      ((Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))).and
        ((hδ.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))).and
          ((hLoss.eventually (eventually_gt_nhds hbr')).and
            (tendsto_cutoff_atTop.eventually (eventually_ge_atTop (Real.log 3 / g))))))
  obtain ⟨H₀, hh⟩ := eventually_atTop.mp hevent
  have hlogT : Tendsto (fun N : ℕ ↦ Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hlogT.eventually (eventually_ge_atTop H₀))
  refine ⟨N₀, ?_⟩
  intro N hN Y hY hcut
  let H := Real.log (N : ℝ)
  let V := saddleCutoff 1 H
  let δ := (r / (2 * a)) * (Real.log H / V)
  let σ := 1 - δ
  obtain ⟨hbase, hlog, hδhalf, hL, hVlarge⟩ := hh H (hN₀ N (by omega))
  have hHE : HE ≤ H := (le_max_left _ _).trans hbase
  have hHB : HB ≤ H := (le_max_left _ _).trans ((le_max_right _ _).trans hbase)
  obtain ⟨hHp, hVp, _hVlo, _hVhi⟩ := hbnd H hHB
  have hlogp : 0 < Real.log H := by linarith only [hlog]
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hδpos : 0 < δ := by dsimp only [δ]; positivity
  have hσ : 1 / 2 ≤ σ := by dsimp only [σ]; linarith only [hδhalf]
  have hσ1 : σ ≤ 1 := by dsimp only [σ]; linarith only [hδpos]
  have hDelta : 1 - σ = δ := by dsimp only [σ]; ring
  have hid : δ = r * Real.log H / (2 * a * V) := by
    dsimp only [δ]
    field_simp
  have hEuler : PrimeHarmonicUpper.constant * (Y : ℝ) ^ δ *
      (1 + Real.log (Real.log ((Y : ℝ) + 2))) ≤ g * V := by
    rw [hid]
    exact he H hHE Y hY hcut
  have hLossFinite : b₁ * V ≤ H * δ := by
    have hx := mul_le_mul_of_nonneg_left hL.le hVp.le
    have heq : V * ((r / (2 * a)) * (H * Real.log H / V ^ 2)) = H * δ := by
      dsimp only [δ]
      field_simp
    change V * b₁ ≤ V * ((r / (2 * a)) * (H * Real.log H / V ^ 2)) at hx
    rw [heq] at hx
    nlinarith only [hx]
  have hNpow : (N : ℝ) ^ σ ≤ (N : ℝ) * Real.exp (-b₁ * V) := by
    rw [Real.rpow_def_of_pos hn]
    have hexp : H * σ ≤ H + -b₁ * V := by dsimp only [σ]; nlinarith only [hLossFinite]
    calc
      _ ≤ Real.exp (H + -b₁ * V) := Real.exp_le_exp.mpr hexp
      _ = _ := by rw [Real.exp_add, Real.exp_log hn]
  have hthree : ((3 * N : ℕ) : ℝ) ^ σ ≤ 3 * (N : ℝ) ^ σ := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hn.le]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_self_of_one_le (by norm_num : (1 : ℝ) ≤ 3) hσ1) (Real.rpow_nonneg hn.le _)
  have hcount := PrimeHarmonicUpper.pivot_count_uniform (3 * N) Y hY σ hσ hσ1
  rw [hDelta] at hcount
  have hpref : 3 ≤ Real.exp (g * V) := by
    have hx := (div_le_iff₀ hg).mp hVlarge
    calc
      _ = Real.exp (Real.log 3) := (Real.exp_log (by norm_num : (0 : ℝ) < 3)).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith only [hx])
  calc
    _ ≤ ((3 * N : ℕ) : ℝ) ^ σ * Real.exp (PrimeHarmonicUpper.constant * (Y : ℝ) ^ δ *
        (1 + Real.log (Real.log ((Y : ℝ) + 2)))) := hcount
    _ ≤ (3 * ((N : ℝ) * Real.exp (-b₁ * V))) * Real.exp (g * V) :=
      mul_le_mul (hthree.trans (mul_le_mul_of_nonneg_left hNpow (by norm_num)))
        (Real.exp_le_exp.mpr hEuler) (Real.exp_nonneg _) (by positivity)
    _ = 3 * N * Real.exp ((-b₁ + g) * V) := by
      rw [show 3 * ((N : ℝ) * Real.exp (-b₁ * V)) * Real.exp (g * V) =
        3 * N * (Real.exp (-b₁ * V) * Real.exp (g * V)) by ring, ← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp (g * V) * N * Real.exp ((-b₁ + g) * V) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpref hn.le) (Real.exp_nonneg _)
    _ = (N : ℝ) * (Real.exp (g * V) * Real.exp ((-b₁ + g) * V)) := by ring
    _ = _ := by rw [← Real.exp_add]; congr 2; dsimp only [g]; ring

theorem uniform_population_bound (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : b < 1 / a) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ S : Finset ℕ,
      S ⊆ Finset.Icc 1 (3 * N) →
      (∀ n ∈ S, (largestOddPrime n : ℝ) ≤ Real.exp (a * saddleCutoff 1 (Real.log N))) →
        (S.card : ℝ) ≤ (N : ℝ) * Real.exp (-b * saddleCutoff 1 (Real.log N)) := by
  obtain ⟨NC, hc⟩ := uniform_count a b ha hb hab
  have hlogT : Tendsto (fun N : ℕ ↦ Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hVT := (tendsto_cutoff_atTop.comp hlogT).const_mul_atTop ha
  obtain ⟨NG, hg⟩ := eventually_atTop.mp (hVT.eventually (eventually_ge_atTop (1 : ℝ)))
  refine ⟨max NC NG, ?_⟩
  intro N hN S hS hcut
  let Y := ⌊Real.exp (a * saddleCutoff 1 (Real.log N))⌋₊
  have hscale := hg N (by omega)
  change 1 ≤ a * saddleCutoff 1 (Real.log N) at hscale
  have he : 2 ≤ Real.exp (a * saddleCutoff 1 (Real.log N)) := by
    have hh := Real.add_one_le_exp (a * saddleCutoff 1 (Real.log N))
    linarith only [hh, hscale]
  have hY : 2 ≤ Y := (Nat.le_floor_iff (Real.exp_nonneg _)).mpr (by simpa only [Nat.cast_ofNat] using he)
  have hsub : S ⊆ pivotValues (3 * N) Y := by
    intro n hn
    apply Finset.mem_filter.mpr
    exact ⟨hS hn, (Nat.le_floor_iff (Real.exp_nonneg _)).mpr (hcut n hn)⟩
  have hh : (S.card : ℝ) ≤ ((pivotValues (3 * N) Y).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
  exact hh.trans (hc N (by omega) Y hY (Nat.floor_le (Real.exp_nonneg _)))

end PaperP1.ScaledSaddlePivotCount
