module

public import PaperP1.Asymptotics.LogarithmicOrdinaryCensusBridge
public import PaperP1.Analysis.GaussianLogarithmicScales


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.LogarithmicGaussianWindowScales
open Filter PaperP1 LogarithmicOrdinaryCensusBridge
open scoped Classical

def slope : ℝ := 1/(8*Real.log 2)

def tailRate : ℝ := slope^2/1152

theorem slope_pos : 0 < slope := by unfold slope; positivity

theorem tailRate_pos : 0 < tailRate := by unfold tailRate; positivity [slope_pos]

theorem window_upper (N : ℕ) (hN : 1 ≤ N) :
    (windowLength N : ℝ) ≤ Real.log (N : ℝ)/(4*Real.log 2) :=
  Nat.floor_le (div_nonneg (Real.log_nonneg (by exact_mod_cast hN)) (by positivity))

theorem window_lower (N : ℕ) (hLog : 8*Real.log 2 ≤ Real.log (N : ℝ)) :
    slope*Real.log (N : ℝ) ≤ (windowLength N : ℝ) := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hRatio : (2 : ℝ) ≤ Real.log (N : ℝ)/(4*Real.log 2) :=
    (le_div_iff₀ (by positivity : 0 < 4*Real.log 2)).mpr (by linarith only [hLog])
  have hFloor := Nat.lt_floor_add_one (Real.log (N : ℝ)/(4*Real.log 2))
  have hSlope : slope*Real.log (N : ℝ)=(Real.log (N : ℝ)/(4*Real.log 2))/2 := by
    unfold slope
    ring
  rw [hSlope]
  change (Real.log (N : ℝ)/(4*Real.log 2))/2 ≤ (⌊Real.log (N : ℝ)/(4*Real.log 2)⌋₊ : ℝ)
  linarith only [hFloor,hRatio]

theorem relative_length_tendsto :
    Tendsto (fun N : ℕ ↦ (windowLength N : ℝ)/(N : ℝ)) atTop (nhds 0) := by
  have hLimit : Tendsto (fun N : ℕ ↦ (Real.log (N : ℝ)/(4*Real.log 2))/(N : ℝ)) atTop (nhds 0) := by
    simpa only [zero_div,div_div,mul_comm] using GaussianLogarithmicScales.logarithmic_ratio_tendsto.div_const (4*Real.log 2)
  apply squeeze_zero' (Filter.Eventually.of_forall (fun N ↦ by positivity))
    ((eventually_ge_atTop 1).mono (fun N hN ↦
      div_le_div_of_nonneg_right (window_upper N hN) (Nat.cast_nonneg N))) hLimit

theorem eventual_geometry (D : ℝ) (hD : 0 < D) : ∀ᶠ N : ℕ in atTop,
    2 ≤ N ∧ 6 ≤ windowLength N ∧ windowLength N ≤ N ∧
      Real.log (N : ℝ)/(D*(N : ℝ)) ≤ 1 ∧
      1 ≤ (N : ℝ)*(Real.log (N : ℝ)/(D*(N : ℝ))) ∧
      8*Real.log 2 ≤ Real.log (N : ℝ) := by
  have hDelta : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)/(D*(N : ℝ))) atTop (nhds 0) := by
    simpa only [zero_div,div_div,mul_comm] using GaussianLogarithmicScales.logarithmic_ratio_tendsto.div_const D
  have hLogLimit := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_ge_atTop 2,window_grows.eventually (eventually_ge_atTop 6),
    relative_length_tendsto.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ)<1)),
    hDelta.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ)<1)),
    hLogLimit.eventually (eventually_ge_atTop (max D (8*Real.log 2)))]
    with N hN hW hRel hDel hLog
  have hNP : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0<N)
  have hLogD : D ≤ Real.log (N : ℝ) := (le_max_left _ _).trans hLog
  have hNat : windowLength N ≤ N := by
    exact_mod_cast (div_le_one hNP).mp hRel.le
  have hMass : 1 ≤ (N : ℝ)*(Real.log (N : ℝ)/(D*(N : ℝ))) := by
    have hh : 1 ≤ Real.log (N : ℝ)/D := (le_div_iff₀ hD).mpr (by simpa only [one_mul] using hLogD)
    have he : (N : ℝ)*(Real.log (N : ℝ)/(D*(N : ℝ)))=Real.log (N : ℝ)/D := by field_simp
    rw [he]
    exact hh
  exact ⟨hN,hW,hNat,hDel.le,hMass,(le_max_right _ _).trans hLog⟩

theorem tail_exponent_lower (D : ℝ) (hD : 0 < D) (N : ℕ) (hN : 2 ≤ N)
    (hLog : 8*Real.log 2 ≤ Real.log (N : ℝ)) :
    tailRate*D^2 ≤ ((windowLength N : ℝ)/(12*(N : ℝ)))^2/
      (8*(Real.log (N : ℝ)/(D*(N : ℝ)))^2) := by
  have hNP : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0<N)
  have hLP : 0 < Real.log (N : ℝ) :=
    (by positivity : 0 < 8*Real.log 2).trans_le hLog
  have hRatio : slope ≤ (windowLength N : ℝ)/Real.log (N : ℝ) :=
    (le_div_iff₀ hLP).mpr (window_lower N hLog)
  have hPow := pow_le_pow_left₀ (by positivity [slope_pos] : 0 ≤ D*slope)
    (mul_le_mul_of_nonneg_left hRatio hD.le) 2
  calc
    _ = (D*slope)^2/1152 := by unfold tailRate; ring
    _ ≤ (D*((windowLength N : ℝ)/Real.log (N : ℝ)))^2/1152 :=
      div_le_div_of_nonneg_right hPow (by norm_num)
    _ = _ := by field_simp; ring

end PaperP1.LogarithmicGaussianWindowScales
