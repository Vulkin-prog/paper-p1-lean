module

public import PaperP1.Analysis.FixedPowerPrimeBand


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.FixedPowerSamplingGeometry
open Finset Filter PaperP1
open scoped Classical

theorem logarithmic_comparison (a X u : ℝ) (ha : 0 < a) (hX : 1 < X) (hLower : X^(a/2) ≤ u) :
    0 < Real.log u ∧ Real.log X ≤ (2/a)*Real.log u := by
  have hXP : 0 < X := by linarith only [hX]
  have hLogX : 0 < Real.log X := Real.log_pos hX
  have hLog := Real.log_le_log (Real.rpow_pos_of_pos hXP (a/2)) hLower
  rw [Real.log_rpow hXP] at hLog
  have hLogU : 0 < Real.log u := (mul_pos (div_pos ha (by norm_num)) hLogX).trans_le hLog
  have hh := mul_le_mul_of_nonneg_left hLog (by positivity : 0 ≤ 2/a)
  have he : (2/a)*((a/2)*Real.log X)=Real.log X := by field_simp [ha.ne']
  rw [he] at hh
  exact ⟨hLogU,hh⟩

theorem height_power_bound (a X u : ℝ) (ha : 0 < a) (hX : 2 ≤ X) (hLower : X^(a/2) ≤ u) :
    2*X ≤ u^(4/a) := by
  have hXP : 0 < X := by linarith only [hX]
  have hPower := Real.rpow_le_rpow (Real.rpow_nonneg hXP.le (a/2)) hLower (by positivity : 0 ≤ 4/a)
  rw [← Real.rpow_mul hXP.le,show (a/2)*(4/a)=2 by field_simp [ha.ne']; norm_num,Real.rpow_two] at hPower
  exact (by nlinarith only [hX] : 2*X ≤ X^2).trans hPower

theorem cardinality_eventually (a C : ℝ) (ha : 0 < a) (hC : 0 ≤ C) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ u : ℝ, (N : ℝ)^(a/2) ≤ u →
      ∀ m : ℝ, m ≤ (Real.log (N : ℝ))^C → m ≤ (Real.log u)^(C+1) := by
  have hLimit := Real.tendsto_log_atTop.comp (FixedPowerPrimeBand.lower_tendsto (a/2) (by positivity))
  obtain ⟨N₁,hN₁⟩ := eventually_atTop.mp (hLimit.eventually (eventually_ge_atTop (max 1 ((2/a)^C))))
  refine ⟨max 2 N₁,le_max_left _ _,?_⟩
  intro N hN u hLower m hCard
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hNR : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNP : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨hLogU,hScale⟩ := logarithmic_comparison a N u ha hNR hLower
  have hBase := hN₁ N ((le_max_right _ _).trans hN)
  have hLogMono := Real.log_le_log (Real.rpow_pos_of_pos hNP (a/2)) hLower
  have hK : (2/a)^C ≤ Real.log u := (le_max_right _ _).trans (hBase.trans hLogMono)
  calc
    m ≤ (Real.log (N : ℝ))^C := hCard
    _ ≤ ((2/a)*Real.log u)^C := Real.rpow_le_rpow (Real.log_pos hNR).le hScale hC
    _ = (2/a)^C*(Real.log u)^C := Real.mul_rpow (by positivity : 0 ≤ 2/a) hLogU.le
    _ ≤ Real.log u*(Real.log u)^C := mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg hLogU.le C)
    _ = _ := by rw [Real.rpow_add hLogU,Real.rpow_one]; ring

theorem scale_eventually (a A₀ : ℝ) (ha : 0 < a) :
    ∀ᶠ N : ℕ in atTop, ∀ u : ℝ, (N : ℝ)^(a/2) ≤ u → A₀ ≤ u := by
  filter_upwards [(FixedPowerPrimeBand.lower_tendsto (a/2) (by positivity)).eventually (eventually_ge_atTop A₀)] with N hN
  intro u hu
  exact hN.trans hu

theorem logarithmic_square_bound (a X u : ℝ) (ha : 0 < a) (hX : 1 < X) (hLower : X^(a/2) ≤ u) :
    1/(Real.log u)^2 ≤ (4/a^2)/(Real.log X)^2 := by
  have hXP : 0 < X := by linarith only [hX]
  have hLogX : 0 < Real.log X := Real.log_pos hX
  have hLog := Real.log_le_log (Real.rpow_pos_of_pos hXP (a/2)) hLower
  rw [Real.log_rpow hXP] at hLog
  have hProduct : 0 < (a/2)*Real.log X := by positivity
  have hSquare := pow_le_pow_left₀ hProduct.le hLog 2
  calc
    _ ≤ 1/(((a/2)*Real.log X)^2) := one_div_le_one_div_of_le (sq_pos_of_pos hProduct) hSquare
    _ = _ := by field_simp [ha.ne',hLogX.ne']; norm_num
end PaperP1.FixedPowerSamplingGeometry
