module

public import Mathlib.Analysis.Real.Sqrt
public import PaperP1.Analysis.SmoothIntervalProfile
public import PaperP1.Analysis.SmoothPrefixComparison
public import PaperP1.Analysis.SmoothRoughPopulation


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.SmoothLongMeanStability
open Finset Nat Filter PaperP1 SmoothPrefixComparison SmoothRoughPopulation
  SmoothIntervalProfile MultiplicativeShortAverage
open scoped Classical

def length (N : ℕ) : ℕ := ⌈(N : ℝ)/Real.sqrt (Real.log (N : ℝ))⌉₊

def error (a : ℝ) (N : ℕ) : ℝ :=
  2*constant a/Real.sqrt (Real.log (N : ℝ))+2*constant a/Real.log (N : ℝ)

theorem length_pos (N : ℕ) (hN : 2 ≤ N) : 0 < length N := by
  have hNR : 1 < (N : ℝ) := by exact_mod_cast (by omega : 1<N)
  apply Nat.one_le_ceil_iff.mpr
  exact div_pos (by linarith only [hNR]) (Real.sqrt_pos.mpr (Real.log_pos hNR))

theorem length_le (N : ℕ) (hN : 0 ≤ (N : ℝ)) (hLog : 1 ≤ Real.log (N : ℝ)) : length N ≤ N := by
  apply Nat.ceil_le.mpr
  exact div_le_self hN (by
    have hh := Real.sqrt_le_sqrt hLog
    simpa only [Real.sqrt_one] using hh)

theorem length_lower (N : ℕ) :
    (N : ℝ)/Real.sqrt (Real.log (N : ℝ)) ≤ (length N : ℝ) := Nat.le_ceil _

theorem error_tendsto (a : ℝ) : Tendsto (error a) atTop (nhds 0) := by
  have hLog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hSqrt := Real.tendsto_sqrt_atTop.comp hLog
  have hOne : Tendsto (fun N : ℕ ↦ 2*constant a/Real.sqrt (Real.log (N : ℝ))) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hSqrt
  have hTwo : Tendsto (fun N : ℕ ↦ 2*constant a/Real.log (N : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hLog
  change Tendsto (fun N : ℕ ↦ 2*constant a/Real.sqrt (Real.log (N : ℝ))+
    2*constant a/Real.log (N : ℝ)) atTop (nhds 0)
  simpa only [zero_add] using hOne.add hTwo

theorem quantitative_bound (a : ℝ) (ha : 0 < a) : ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀,
    ∀ j ∈ Ico N (2*N),
      |shortMean (OrdinarySmoothIndicator.value ⌊(N : ℝ)^a⌋₊) j (length N)-
        longMean (OrdinarySmoothIndicator.value ⌊(N : ℝ)^a⌋₊) N| ≤ error a N := by
  obtain ⟨NR,hNR,hRough⟩ := SmoothRoughPopulation.eventual_bound a ha
  have hLogLimit := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨NL,hLogTail⟩ := eventually_atTop.mp (hLogLimit.eventually (eventually_ge_atTop (1 : ℝ)))
  refine ⟨max NR NL,by omega,?_⟩
  intro N hN j hj
  have hNN : 2 ≤ N := by omega
  have hNP : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0<N)
  have hLog1 : 1 ≤ Real.log (N : ℝ) := hLogTail N (by omega)
  have hLog : 0 < Real.log (N : ℝ) := by linarith only [hLog1]
  have hSqrt : 0 < Real.sqrt (Real.log (N : ℝ)) := Real.sqrt_pos.mpr hLog
  have hh : 0 < length N := length_pos N hNN
  have hhR : 0 < (length N : ℝ) := by exact_mod_cast hh
  have hY : 1 ≤ ⌊(N : ℝ)^a⌋₊ :=
    PowerSelbergLevel.level_pos a (N : ℝ) ha.le (by exact_mod_cast (by omega : 1≤N))
  have hLength : length N ≤ N := length_le N hNP.le hLog1
  have hBound := short_long_bound ⌊(N : ℝ)^a⌋₊ (4*N) N j (length N) hY (by omega)
    (by have := (mem_Ico.mp hj).1; omega) hh
    (by have := (mem_Ico.mp hj).2; omega) (by omega)
  have hR := hRough N (by omega)
  have hC := constant_pos a ha
  have hFirst : 2*((roughSet ⌊(N : ℝ)^a⌋₊ (4*N)).card : ℝ)/(length N : ℝ) ≤
      2*constant a/Real.sqrt (Real.log (N : ℝ)) := by
    calc
      _ ≤ (2*(constant a*(N : ℝ)/Real.log (N : ℝ)))/(length N : ℝ) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hR (by norm_num)) hhR.le
      _ ≤ (2*(constant a*(N : ℝ)/Real.log (N : ℝ)))/
          ((N : ℝ)/Real.sqrt (Real.log (N : ℝ))) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (length_lower N)
      _ = _ := by
        have hSq := Real.sq_sqrt hLog.le
        field_simp
        nlinarith only [hSq]
  have hSecond : 2*((roughSet ⌊(N : ℝ)^a⌋₊ (4*N)).card : ℝ)/(N : ℝ) ≤
      2*constant a/Real.log (N : ℝ) := by
    calc
      _ ≤ (2*(constant a*(N : ℝ)/Real.log (N : ℝ)))/(N : ℝ) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hR (by norm_num)) hNP.le
      _ = _ := by field_simp
  exact hBound.trans (add_le_add hFirst hSecond)

theorem uniform_bound (a : ℝ) (ha : 0 < a) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ j ∈ Ico N (2*N),
      |shortMean (OrdinarySmoothIndicator.value ⌊(N : ℝ)^a⌋₊) j (length N)-
        longMean (OrdinarySmoothIndicator.value ⌊(N : ℝ)^a⌋₊) N| ≤ ε := by
  obtain ⟨NB,hNB,hBound⟩ := quantitative_bound a ha
  obtain ⟨NE,hError⟩ := eventually_atTop.mp ((error_tendsto a).eventually (eventually_lt_nhds hε))
  refine ⟨max NB NE,by omega,?_⟩
  intro N hN j hj
  exact (hBound N (by omega) j hj).trans (hError N (by omega)).le

end PaperP1.SmoothLongMeanStability
