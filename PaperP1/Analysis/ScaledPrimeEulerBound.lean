module

public import PaperP1.Arithmetic.PrimeHarmonicUpper
public import PaperP1.Analysis.HardSaddleGrowth
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Prime Euler bounds at every fixed positive multiple of the hard saddle -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ScaledPrimeEulerBound

open Filter SaddleParameters SaddleScales HardSaddleGrowth

theorem finite_exponent_bound (a r C H V : ℝ) (ha : 0 < a) (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hH : 4 ≤ H) (hlog : 1 ≤ Real.log H) (hV : 0 < V) (hVH : V ≤ H) (haV : 1 ≤ a * V)
    (Y : ℕ) (hY : 2 ≤ Y) (hcut : (Y : ℝ) ≤ Real.exp (a * V)) :
    C * (Y : ℝ) ^ (r * Real.log H / (2 * a * V)) * (1 + Real.log (Real.log ((Y : ℝ) + 2))) ≤
      (C * (2 + Real.log (a + 1))) * H ^ (r / 2) * Real.log H := by
  have hHp : 0 < H := by linarith only [hH]
  have hlogp : 0 < Real.log H := by linarith only [hlog]
  have hlogA : 0 < Real.log (a + 1) := Real.log_pos (by linarith only [ha])
  have hYpow : (Y : ℝ) ^ (r * Real.log H / (2 * a * V)) ≤ H ^ (r / 2) := by
    calc
      _ ≤ (Real.exp (a * V)) ^ (r * Real.log H / (2 * a * V)) :=
        Real.rpow_le_rpow (Nat.cast_nonneg Y) hcut (by positivity)
      _ = Real.exp (Real.log H * (r / 2)) := by
        rw [← Real.exp_mul]
        congr 1
        field_simp
      _ = _ := (Real.rpow_def_of_pos hHp _).symm
  have he : 2 ≤ Real.exp (a * V) := by have hh := Real.add_one_le_exp (a * V); linarith only [hh, haV]
  have hYplus : (Y : ℝ) + 2 ≤ 2 * Real.exp (a * V) := by linarith only [hcut, he]
  have hlog2 : Real.log 2 ≤ 1 :=
    (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)).trans (by norm_num)
  have hlogY : Real.log ((Y : ℝ) + 2) ≤ (a + 1) * H := by
    have hh := mul_le_mul_of_nonneg_left hVH ha.le
    calc
      _ ≤ Real.log (2 * Real.exp (a * V)) := Real.log_le_log (by positivity) hYplus
      _ = Real.log 2 + a * V := by rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_ne_zero _), Real.log_exp]
      _ ≤ _ := by nlinarith only [hh, hH, hlog2]
  have hlogYpos : 0 < Real.log ((Y : ℝ) + 2) := Real.log_pos (by
    have hy : (2 : ℝ) ≤ Y := by exact_mod_cast hY
    linarith only [hy])
  have houter : Real.log (Real.log ((Y : ℝ) + 2)) ≤ Real.log (a + 1) + Real.log H := by
    calc
      _ ≤ Real.log ((a + 1) * H) := Real.log_le_log hlogYpos hlogY
      _ = _ := Real.log_mul (by positivity : a + 1 ≠ 0) hHp.ne'
  have hfactor : 1 + Real.log (Real.log ((Y : ℝ) + 2)) ≤ (2 + Real.log (a + 1)) * Real.log H := by
    have hh := mul_nonneg (by linarith only [hlogA] : 0 ≤ 1 + Real.log (a + 1))
      (by linarith only [hlog] : 0 ≤ Real.log H - 1)
    nlinarith only [hh, houter]
  calc
    _ ≤ C * (Y : ℝ) ^ (r * Real.log H / (2 * a * V)) * ((2 + Real.log (a + 1)) * Real.log H) :=
      mul_le_mul_of_nonneg_left hfactor (by positivity)
    _ ≤ C * H ^ (r / 2) * ((2 + Real.log (a + 1)) * Real.log H) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hYpow hC) (by positivity)
    _ = _ := by ring

theorem eventual_exponent_bound (a r η : ℝ) (ha : 0 < a) (hr : 0 ≤ r) (hr1 : r < 1) (hη : 0 < η) :
    ∃ H₀ : ℝ, ∀ H ≥ H₀, ∀ Y : ℕ, 2 ≤ Y → (Y : ℝ) ≤ Real.exp (a * saddleCutoff 1 H) →
      PrimeHarmonicUpper.constant * (Y : ℝ) ^ (r * Real.log H / (2 * a * saddleCutoff 1 H)) *
        (1 + Real.log (Real.log ((Y : ℝ) + 2))) ≤ η * saddleCutoff 1 H := by
  let K := PrimeHarmonicUpper.constant * (2 + Real.log (a + 1))
  have hK : 0 < K := by
    have hh : 0 < Real.log (a + 1) := Real.log_pos (by linarith only [ha])
    exact mul_pos PrimeHarmonicUpper.constant_pos (by linarith only [hh])
  let g := (1 - r) / 2
  have hg : 0 < g := by dsimp only [g]; linarith only [hr1]
  have hsmall := (isLittleO_log_rpow_rpow_atTop (1 : ℝ) hg).bound (div_pos hη hK)
  obtain ⟨HB, hb⟩ := square_band_eventually
  have hevent : ∀ᶠ H : ℝ in atTop,
      max HB 4 ≤ H ∧ 1 ≤ Real.log H ∧ saddleCutoff 1 H / H < 1 ∧
      1 / a ≤ saddleCutoff 1 H ∧ ‖Real.log H ^ (1 : ℝ)‖ ≤ (η / K) * ‖H ^ g‖ :=
    (eventually_ge_atTop (max HB 4)).and
      ((Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))).and
        ((tendsto_cutoff_div_height.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))).and
          ((tendsto_cutoff_atTop.eventually (eventually_ge_atTop (1 / a))).and hsmall)))
  obtain ⟨H₀, h⟩ := eventually_atTop.mp hevent
  refine ⟨H₀, ?_⟩
  intro H hH Y hY hcut
  obtain ⟨hbase, hlog, hVH, haV, hs⟩ := h H hH
  obtain ⟨hHp, hVp, hsq, _hsq⟩ := hb H ((le_max_left _ _).trans hbase)
  have hH4 : 4 ≤ H := (le_max_right _ _).trans hbase
  have hVH' : saddleCutoff 1 H ≤ H := by
    have hh := (div_le_iff₀ hHp).mp hVH.le
    simpa only [one_mul] using hh
  have haV' : 1 ≤ a * saddleCutoff 1 H := by
    have hh := (div_le_iff₀ ha).mp haV
    nlinarith only [hh]
  have hroot : Real.sqrt H ≤ saddleCutoff 1 H := by
    have hh := Real.sq_sqrt hHp.le
    have hz := Real.sqrt_nonneg H
    nlinarith only [hsq, hh, hz, hVp]
  have hs' : Real.log H ≤ (η / K) * H ^ g := by
    simpa only [Real.rpow_one, Real.norm_eq_abs,
      abs_of_nonneg (by linarith only [hlog] : 0 ≤ Real.log H),
      abs_of_nonneg (Real.rpow_nonneg hHp.le g)] using hs
  calc
    _ ≤ K * H ^ (r / 2) * Real.log H :=
      finite_exponent_bound a r _ H _ ha hr PrimeHarmonicUpper.constant_pos.le hH4 hlog hVp hVH' haV' Y hY hcut
    _ ≤ K * H ^ (r / 2) * ((η / K) * H ^ g) := mul_le_mul_of_nonneg_left hs' (by positivity)
    _ = η * (H ^ (r / 2) * H ^ g) := by field_simp
    _ = η * Real.sqrt H := by
      rw [← Real.rpow_add hHp]
      dsimp only [g]
      rw [show r / 2 + (1 - r) / 2 = (1 / 2 : ℝ) by ring, ← Real.sqrt_eq_rpow]
    _ ≤ _ := mul_le_mul_of_nonneg_left hroot hη.le

end PaperP1.ScaledPrimeEulerBound
