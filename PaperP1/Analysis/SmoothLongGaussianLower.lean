module

public import PaperP1.Analysis.PolynomialSmoothDyadicDensity
public import PaperP1.Analysis.LogarithmicWindowCells
public import PaperP1.Analysis.SmoothGaussianPopulation


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.SmoothLongGaussianLower
open Finset Filter PaperP1 OddPrimePivot GaussianLaplaceKernel SmoothGaussianPopulation
  MultiplicativeShortAverage SmoothLongMeanStability
open scoped Classical

theorem uniform_lower (a : ℝ) (ha : 0 < a) : ∃ κ : ℝ, 0 < κ ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧
    ∀ N ≥ N₀, ∀ X : ℝ, (N : ℝ) ≤ X → X+1 ≤ 2*(N : ℝ) →
      κ ≤ ActualGaussianMeanComparison.smoothed N (OrdinarySmoothIndicator.value ⌊(N : ℝ)^a⌋₊)
        (GaussianLogarithmicScales.longWidth N) (-Real.log X) := by
  obtain ⟨ρ,hρ,ND,hDensity⟩ := PolynomialSmoothDyadicDensity.uniform_lower a ha
  obtain ⟨NB,hNB,hBound⟩ := SmoothLongMeanStability.uniform_bound a ha (ρ/2) (by positivity)
  have hLogLimit := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨NL,hLog⟩ := eventually_atTop.mp (hLogLimit.eventually (eventually_ge_atTop (1 : ℝ)))
  refine ⟨ρ*(prefactor 1*Real.exp (-1))/8,by positivity [prefactor_pos 1 (by norm_num)],
    max 2 (max ND (max NB NL)),by omega,?_⟩
  intro N hN X hXL hXU
  have hNN : 2 ≤ N := by omega
  have hNP : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0<N)
  have hX : 0 < X := hNP.trans_le hXL
  let Y := ⌊(N : ℝ)^a⌋₊
  let j : ℕ := ⌈X⌉₊
  let h : ℕ := length N
  have hh : 0 < h := length_pos N hNN
  have hhR : 0 < (h : ℝ) := by exact_mod_cast hh
  have hLength : h ≤ N := length_le N hNP.le (hLog N (by omega))
  have hJLower : X ≤ (j : ℝ) := Nat.le_ceil X
  have hJUpper : (j : ℝ) < X+1 := Nat.ceil_lt_add_one hX.le
  have hjN : N ≤ j := by exact_mod_cast hXL.trans hJLower
  have hjU : j<2*N := by exact_mod_cast hJUpper.trans_le hXU
  have hjBand : j ∈ Ico N (2*N) := mem_Ico.mpr ⟨hjN,hjU⟩
  have hLong : ρ ≤ longMean (OrdinarySmoothIndicator.value Y) N := by
    rw [longMean,OrdinarySmoothIndicator.dyadic_sum N Y (by omega)]
    exact (le_div_iff₀ hNP).mpr (hDensity N (by omega))
  have hShort : ρ/2 ≤ shortMean (OrdinarySmoothIndicator.value Y) j h := by
    have hhB := hBound N (by omega) j hjBand
    have hAbs := (abs_le.mp hhB).1
    change -(ρ/2) ≤ shortMean (OrdinarySmoothIndicator.value Y) j h-
      longMean (OrdinarySmoothIndicator.value Y) N at hAbs
    linarith only [hLong,hAbs]
  let I : Finset ℕ := (Ico j (j+h)).filter fun n ↦ largestPrimeFactor n ≤ Y
  have hCount : (ρ/2)*(h : ℝ) ≤ (I.card : ℝ) := by
    have hSum : (∑ r ∈ range h, OrdinarySmoothIndicator.value Y (j+r))=(I.card : ℝ) := by
      have hhSum := OrdinarySmoothIndicator.sum_eq_filter_card Y (Ico j (j+h)) (by
        intro n hn
        have hnL := (mem_Ico.mp hn).1
        omega)
      rw [sum_Ico_eq_sum_range,Nat.add_sub_cancel_left] at hhSum
      exact hhSum
    change (ρ/2)*(h : ℝ) ≤ (I.card : ℝ)
    exact (le_div_iff₀ hhR).mp (by simpa only [shortMean,hSum] using hShort)
  have hIS : I ⊆ population N Y := by
    intro n hn
    obtain ⟨hnI,hnSmooth⟩ := mem_filter.mp hn
    have hnB := mem_Ico.mp hnI
    exact mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega,by omega⟩,hnSmooth⟩
  have hNear : ∀ n ∈ I, |Real.log ((n : ℝ)/X)| ≤ (h : ℝ)/(N : ℝ) := by
    intro n hn
    have hnI := mem_Ico.mp (mem_filter.mp hn).1
    have hnL : X ≤ (n : ℝ) := hJLower.trans (by exact_mod_cast hnI.1)
    have hnTop : (n : ℝ) < X+(h : ℝ) := by
      have hhInt : (n : ℝ) < (j : ℝ)+(h : ℝ) := by exact_mod_cast hnI.2
      have hnNat : n+1 ≤ j+h := by omega
      have hnReal : (n : ℝ)+1 ≤ (j : ℝ)+(h : ℝ) := by exact_mod_cast hnNat
      linarith only [hnReal,hJUpper]
    have hGap := LogarithmicWindowCells.log_ratio_upper (N : ℝ) X (n : ℝ) hNP hXL
      (by exact_mod_cast (by omega : N≤n))
    rw [abs_of_nonneg (sub_nonneg.mpr hnL)] at hGap
    exact hGap.trans (div_le_div_of_nonneg_right (by linarith only [hnTop] : (n : ℝ)-X ≤ h) hNP.le)
  have hLower := subpopulation_lower N Y (by omega) I hIS X ((h : ℝ)/(N : ℝ)) hX (by positivity) hNear
  have hCardLower := mul_le_mul_of_nonneg_right hCount
    (by positivity [prefactor_pos 1 (by norm_num)] : 0 ≤ (prefactor 1*Real.exp (-1))/
      (((h : ℝ)/(N : ℝ))*(4*(N : ℝ))))
  have hConst : (ρ/2)*(h : ℝ)*((prefactor 1*Real.exp (-1))/
      (((h : ℝ)/(N : ℝ))*(4*(N : ℝ)))) = ρ*(prefactor 1*Real.exp (-1))/8 := by
    field_simp
    ring
  rw [hConst] at hCardLower
  change ρ*(prefactor 1*Real.exp (-1))/8 ≤
    ActualGaussianMeanComparison.smoothed N (OrdinarySmoothIndicator.value Y)
      (((h : ℝ)/(N : ℝ))^2) (-Real.log X)
  exact hCardLower.trans (by simpa only [mul_div_assoc] using hLower)

end PaperP1.SmoothLongGaussianLower
