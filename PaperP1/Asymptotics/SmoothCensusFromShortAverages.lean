module

public import PaperP1.Arithmetic.OrdinarySmoothIndicator
public import PaperP1.Analysis.MultiplicativeShortAverage
public import PaperP1.Analysis.PolynomialSmoothDyadicDensity
public import PaperP1.Asymptotics.LogarithmicOrdinaryCensusBridge

/-! # The actual almost-all source census follows from uniform short-average concentration and the internal positive smooth density -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmoothCensusFromShortAverages
open PaperP1 Finset Filter NonanchorPivotSelection ForcingExceptionalSets OrdinarySmoothSourcePopulation
  AnchoredObstructionUnderOrdinaryCensus LogarithmicOrdinaryCensusBridge
  MultiplicativeShortAverage
open scoped Classical

theorem ordinary_census (C a : ℝ) (ha : 0 < a)
    (hInput : ConcentrationInput windowLength) : OrdinaryCensusDensity C a := by
  obtain ⟨ρ, hρ, ND, hD⟩ := PolynomialSmoothDyadicDensity.uniform_lower a ha
  obtain ⟨NW, hW⟩ := window_actual C
  have hψ := (tendsto_natCast_atTop_atTop (R := ℝ)).comp window_grows
  obtain ⟨NH, hH⟩ := eventually_atTop.mp (hψ.eventually (eventually_ge_atTop (4 / ρ)))
  intro τ hτ
  obtain ⟨NE, hE⟩ := hInput (ρ / 2) (τ / 2) (by positivity) (by positivity)
  obtain ⟨NX, hX⟩ := eventually_atTop.mp
    ((tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop (2 / τ)))
  refine ⟨max 2 (max ND (max NW (max NH (max NE NX)))), ?_⟩
  intro N hN L i hband
  have hn : 2 ≤ N := by omega
  let Y := ⌊(N : ℝ) ^ a⌋₊
  let f := OrdinarySmoothIndicator.arithmetic Y
  have hY : 1 ≤ Y := by
    apply (Nat.le_floor_iff (Real.rpow_nonneg (Nat.cast_nonneg N) a)).mpr
    simpa only [Nat.cast_one] using
      Real.one_le_rpow (show (1 : ℝ) ≤ (N : ℝ) by exact_mod_cast (show 1 ≤ N by omega)) ha.le

  have hf : f.IsMultiplicative := OrdinarySmoothIndicator.isMultiplicative Y hY
  have hb : ∀ n, |f n| ≤ 1 := by
    intro n
    change |OrdinarySmoothIndicator.value Y n| ≤ 1
    rw [abs_of_nonneg (OrdinarySmoothIndicator.value_nonneg Y n)]
    exact OrdinarySmoothIndicator.value_le_one Y n
  have hbad := hE N (by omega) f hf hb
  have hlong : ρ ≤ longMean f N := by
    change ρ ≤ (∑ n ∈ Ico N (2*N), OrdinarySmoothIndicator.value Y n) / N
    rw [OrdinarySmoothIndicator.dyadic_sum N Y (by omega)]
    exact (le_div_iff₀ (by exact_mod_cast (show 0 < N by omega) : (0 : ℝ) < N)).mpr (hD N (by omega))
  have hlarge : 4 / ρ ≤ (windowLength N : ℝ) := hH N (by omega)
  have hwin : 0 < windowLength N := by
    have hp : (0 : ℝ) < windowLength N := lt_of_lt_of_le (by positivity) hlarge
    exact_mod_cast hp
  have hNmem : N ∈ boundaryBlock N := (mem_boundaryBlock hn).mpr (by
    change N+1 ∈ Ico N (2*N)
    exact mem_Ico.mpr ⟨by omega, by omega⟩)
  have hwidth : windowLength N ≤ L + i.val + 1 := by
    have hh := hW N (by omega) L hband N hNmem
    omega
  have hsub : missingCandidates N (L+i.val) ((N : ℝ)^a) ⊆
      {N-1} ∪ bad f N (windowLength N) (ρ/2) := by
    intro j hj
    obtain ⟨hjB, hjfew⟩ := mem_filter.mp hj
    by_cases hjedge : j = N-1
    · exact mem_union_left _ (mem_singleton.mpr hjedge)
    · apply mem_union_right
      have hjbounds := mem_Ico.mp ((mem_boundaryBlock hn).mp hjB)
      have hjN : N ≤ j := by omega
      have hjpos : 0 < j := by omega
      have hc := OrdinaryCandidateMonotonicity.card_le (j := j) hwidth
        (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) a))
      have hsmall : (ordinaryIndices j (windowLength N) (Y : ℝ)).card ≤ 1 := by
        exact Nat.le_of_lt_succ (hc.trans_lt hjfew)
      have hshort : shortMean f j (windowLength N) ≤ ρ / 4 := by
        change (∑ r ∈ range (windowLength N), OrdinarySmoothIndicator.value Y (j+r)) /
          (windowLength N : ℝ) ≤ ρ / 4
        rw [OrdinarySmoothIndicator.short_sum j (windowLength N) Y hjpos]
        apply (div_le_iff₀ (by exact_mod_cast hwin : (0 : ℝ) < windowLength N)).mpr
        have hcR : ((ordinaryIndices j (windowLength N) (Y : ℝ)).card : ℝ) ≤ 1 := by exact_mod_cast hsmall
        have hp := (div_le_iff₀ hρ).mp hlarge
        nlinarith
      refine mem_filter.mpr ⟨mem_Ico.mpr ⟨hjN, by omega⟩, ?_⟩
      have hab := neg_le_abs (shortMean f j (windowLength N) - longMean f N)
      nlinarith
  have hcNat := (card_le_card hsub).trans (card_union_le _ _)
  have hc : ((missingCandidates N (L+i.val) ((N : ℝ)^a)).card : ℝ) ≤
      1 + (bad f N (windowLength N) (ρ/2)).card := by
    exact_mod_cast (by simpa only [card_singleton] using hcNat)
  have hscale := (div_le_iff₀ hτ).mp (hX N (by omega))
  nlinarith

theorem ordinary_census_of_mean_square (C a : ℝ) (ha : 0 < a)
    (hInput : MeanSquareInput windowLength) : OrdinaryCensusDensity C a :=
  ordinary_census C a ha (concentration_of_mean_square windowLength hInput)
end SmoothCensusFromShortAverages
