module

public import PaperP1.Analysis.ExponentialPrimeBands
public import PaperP1.Arithmetic.SmoothRecursiveLower
public import PaperP1.Analysis.HardSaddleGrowth

/-! # Closed explicit lower bounds from the internal smooth-density iteration

The exponential prime bands supply all finite recursive inputs. The resulting
ordinary reciprocal lower bound is retained explicitly, including its ceiling.
A subsequent scale comparison is still needed to identify a leading coefficient.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ExponentialSmoothLower

open Finset Filter DefectCounting PrimeLogarithmicBands OrdinarySmoothCensus SmoothRecursiveLower
  ReciprocalOddPivots SaddleParameters SaddleScales HardSaddleGrowth

theorem uniform_lower (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    ∃ b : ℝ, 0 < b ∧ ∃ H₀ : ℝ, ∀ H ≥ H₀, ∀ M : ℕ, 2 ≤ M →
      b * H ≤ 2 * Real.log M →
      (M : ℝ) * (b * H / (2 * Real.log M)) ^ ⌈Real.log M / (a * H)⌉₊ ≤
          (smoothUpTo M ⌊Real.exp H⌋₊).card ∧
        (M : ℝ) * Real.exp (-H + (⌈Real.log M / (a * H)⌉₊ : ℝ) *
          Real.log (b * H / (2 * Real.log M))) ≤ primeSum M := by
  obtain ⟨b, hb, H₁, hband⟩ := ExponentialPrimeBands.exists_band a ha ha1
  refine ⟨b, hb, max H₁ (max 1 (Real.log 2)), ?_⟩
  intro H hH M hM hsmall
  have hH1 : 1 ≤ H := (le_max_left _ _).trans ((le_max_right _ _).trans hH)
  have hHpos : 0 < H := by linarith only [hH1]
  have hlog : 0 < Real.log M := Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  let Y := ⌊Real.exp H⌋₊
  let R := Real.exp (a * H)
  let r := b * H / (2 * Real.log M)
  let k := ⌈Real.log M / (a * H)⌉₊
  have hY : 2 ≤ Y := by
    apply (Nat.le_floor_iff (Real.exp_nonneg H)).mpr
    have hh : Real.log 2 ≤ H := (le_max_right _ _).trans ((le_max_right _ _).trans hH)
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2), Nat.cast_ofNat] using Real.exp_le_exp.mpr hh
  have hR : 0 < R := Real.exp_pos _
  have hr : 0 < r := by dsimp only [r]; positivity
  have hr1 : r ≤ 1 := by dsimp only [r]; exact (div_le_one (by positivity)).mpr hsmall
  obtain ⟨T, hT, hscale, hmass⟩ := hband H ((le_max_left _ _).trans hH)
  have hpaid : 2 * r * Real.log M ≤ ∑ p ∈ T, Real.log p / p := by
    change 2 * r * Real.log M ≤ mass T
    have hid : 2 * r * Real.log M = b * H := by dsimp only [r]; field_simp
    rw [hid]
    exact hmass
  have hcap : (M : ℝ) ≤ (Y : ℝ) * R ^ k := by
    have hk : Real.log M / (a * H) ≤ (k : ℝ) := Nat.le_ceil _
    have hkh := (div_le_iff₀ (mul_pos ha hHpos)).mp hk
    have he : (M : ℝ) ≤ R ^ k := by
      calc
        _ = Real.exp (Real.log M) := (Real.exp_log (by exact_mod_cast (show 0 < M by omega))).symm
        _ ≤ Real.exp ((k : ℝ) * (a * H)) := Real.exp_le_exp.mpr hkh
        _ = _ := by dsimp only [R]; rw [Real.exp_nat_mul]
    exact he.trans (le_mul_of_one_le_left (pow_nonneg hR.le _) (by exact_mod_cast (show 1 ≤ Y by omega)))
  have hdensity := geometric_density_lower M Y hY R r hR hr.le hr1 T hT hscale hpaid
    k M (by omega) le_rfl hcap
  have hrecip := geometric_reciprocal_lower M Y hY R r hR hr.le hr1 T hT hscale hpaid
    k M (by omega) le_rfl hcap
  refine ⟨hdensity, ?_⟩
  change (M : ℝ) * Real.exp (-H + (k : ℝ) * Real.log r) ≤ primeSum M
  calc
    _ = (M : ℝ) * r ^ k / Real.exp H := by
      rw [Real.exp_add, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hr]
      ring
    _ ≤ (M : ℝ) * r ^ k / Y :=
      div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast (show 0 < Y by omega))
        (Nat.floor_le (Real.exp_nonneg H))
    _ ≤ _ := hrecip

theorem uniform_saddle_lower (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    ∃ b : ℝ, 0 < b ∧ ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2,
      (N : ℝ) * Real.exp (-saddleCutoff 1 (Real.log N) +
        (⌈Real.log N / (a * saddleCutoff 1 (Real.log N))⌉₊ : ℝ) *
          Real.log (b * saddleCutoff 1 (Real.log N) / (2 * Real.log N))) ≤ primeSum N := by
  obtain ⟨b, hb, H₀, hl⟩ := uniform_lower a ha ha1
  have hlogT : Tendsto (fun N : ℕ ↦ Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall : Tendsto (fun N : ℕ ↦ (b / 2) *
      (saddleCutoff 1 (Real.log N) / Real.log N)) atTop (nhds 0) := by
    simpa only [mul_zero, Function.comp_apply] using (tendsto_cutoff_div_height.comp hlogT).const_mul (b / 2)
  obtain ⟨N₀, hh⟩ := eventually_atTop.mp
    (((tendsto_cutoff_atTop.comp hlogT).eventually (eventually_ge_atTop H₀)).and
      (hsmall.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))))
  refine ⟨b, hb, N₀, ?_⟩
  intro N hN
  obtain ⟨hH, hr⟩ := hh N (by omega)
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hsmall' : b * saddleCutoff 1 (Real.log N) ≤ 2 * Real.log N := by
    have hh : (b * saddleCutoff 1 (Real.log N) / 2) / Real.log N < 1 := by
      convert hr using 1
      ring
    have hh' := (div_lt_iff₀ hlog).mp hh
    nlinarith only [hh']
  exact (hl _ hH N (by omega) hsmall').2

end PaperP1.ExponentialSmoothLower
