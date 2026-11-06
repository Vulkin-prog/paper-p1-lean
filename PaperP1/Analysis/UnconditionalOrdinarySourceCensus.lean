module

public import PaperP1.Analysis.CompleteSmoothCensusFromShortAverages
public import PaperP1.Analysis.SmoothLogarithmicWindowDensity


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.UnconditionalOrdinarySourceCensus
open Finset Filter PaperP1 OddPrimePivot NonanchorPivotSelection ForcingExceptionalSets
  OrdinarySmoothSourcePopulation AnchoredObstructionUnderOrdinaryCensus LogarithmicOrdinaryCensusBridge
open scoped Classical

theorem window_card (Y j h : ℕ) (hj : 0 < j) :
    ((Ico j (j+h)).filter fun n ↦ largestPrimeFactor n ≤ Y).card =
      (ordinaryIndices j h (Y : ℝ)).card := by
  have hh := OrdinarySmoothIndicator.sum_eq_filter_card Y (Ico j (j+h)) (by
    intro n hn
    have hnL := (mem_Ico.mp hn).1
    omega)
  rw [sum_Ico_eq_sum_range,Nat.add_sub_cancel_left,
    OrdinarySmoothIndicator.short_sum j h Y hj] at hh
  exact_mod_cast hh.symm

theorem ordinary_census (C a : ℝ) (ha : 0 < a) : OrdinaryCensusDensity C a := by
  obtain ⟨NW,hWidth⟩ := window_actual C
  intro τ hτ
  obtain ⟨NB,hNB,hBad⟩ := SmoothLogarithmicWindowDensity.uniform_bound a ha (τ/2) (by positivity)
  obtain ⟨NX,hScale⟩ := eventually_atTop.mp
    ((tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop (2/τ)))
  refine ⟨max 2 (max NW (max NB NX)),?_⟩
  intro N hN L i hBand
  have hNN : 2 ≤ N := by omega
  have hNP : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0<N)
  let Y := ⌊(N : ℝ)^a⌋₊
  have hNmem : N ∈ boundaryBlock N := (mem_boundaryBlock hNN).mpr
    (mem_Ico.mpr ⟨by omega,by omega⟩)
  have hW : windowLength N ≤ L+i.val+1 := by
    have hh := hWidth N (by omega) L hBand N hNmem
    omega
  have hY : (Y : ℝ) ≤ (N : ℝ)^a := Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) a)
  have hSub : missingCandidates N (L+i.val) ((N : ℝ)^a) ⊆
      {N-1} ∪ SmoothLogarithmicWindowDensity.badWindows N Y := by
    intro j hj
    obtain ⟨hjB,hjFew⟩ := mem_filter.mp hj
    by_cases hEdge : j=N-1
    · exact mem_union_left _ (mem_singleton.mpr hEdge)
    · apply mem_union_right
      have hjBound := mem_Ico.mp ((mem_boundaryBlock hNN).mp hjB)
      have hjN : N ≤ j := by omega
      have hjU : j<2*N := by omega
      have hOrd : (ordinaryIndices j (windowLength N) (Y : ℝ)).card ≤ 1 := by
        have hh := OrdinaryCandidateMonotonicity.card_le (j := j) hW hY
        exact Nat.le_of_lt_succ (hh.trans_lt hjFew)
      apply mem_filter.mpr
      refine ⟨mem_Ico.mpr ⟨hjN,hjU⟩,?_⟩
      rw [window_card Y j (windowLength N) (by omega)]
      exact hOrd
  have hNat := (card_le_card hSub).trans (card_union_le _ _)
  have hReal : ((missingCandidates N (L+i.val) ((N : ℝ)^a)).card : ℝ) ≤
      1+((SmoothLogarithmicWindowDensity.badWindows N Y).card : ℝ) := by
    exact_mod_cast (by simpa only [card_singleton] using hNat)
  have hFew := hBad N (by omega)
  change ((SmoothLogarithmicWindowDensity.badWindows N Y).card : ℝ) ≤ (τ/2)*(N : ℝ) at hFew
  have hBig := (div_le_iff₀ hτ).mp (hScale N (by omega))
  linarith only [hReal,hFew,hBig]

end PaperP1.UnconditionalOrdinarySourceCensus
