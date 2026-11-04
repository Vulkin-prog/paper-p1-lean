module

public import PaperP1.Asymptotics.OrdinaryShortIntervalCensusInput
public import PaperP1.Asymptotics.AnchoredObstructionUnderOrdinaryCensus
public import Mathlib.Analysis.SpecificLimits.Basic

/-! # From an independent almost-all short-interval input to the actual source census

CorollarySixLogInput is an explicit unproved input, a fixed-parameter
specialization of the cited ordinary smooth-number asymptotic with
u=2/a and a logarithmic interval length. Every comparison with the
actual moving critical word and translated dyadic source set is proved.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LogarithmicOrdinaryCensusBridge

open Finset Filter PaperP1.Arithmetic PaperP1.NonanchorPivotSelection
  PaperP1.ForcingExceptionalSets PaperP1.OrdinarySmoothSourcePopulation
  PaperP1.OrdinaryShortIntervalCensusInput PaperP1.AnchoredObstructionUnderOrdinaryCensus

def windowLength (j : ℕ) : ℕ := ⌊Real.log j / (4 * Real.log 2)⌋₊

def CorollarySixLogInput (a : ℝ) : Prop :=
  ∃ ρ : ℝ, 0 < ρ ∧ RelativeDensityInput windowLength a ρ

theorem window_grows : Tendsto windowLength atTop atTop := by
  exact tendsto_nat_floor_atTop.comp (Tendsto.atTop_div_const
    (mul_pos (by norm_num : (0 : ℝ) < 4) (Real.log_pos (by norm_num)))
    PaperP1.PrimeLogBudget.log_nat_tendsto_atTop)

theorem window_actual (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ j ∈ boundaryBlock N, windowLength j ≤ L := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨N₀, h₀⟩ := eventually_atTop.mp
    (PaperP1.PrimeLogBudget.log_nat_tendsto_atTop.eventually
      (eventually_ge_atTop ((2 * C + 2) * Real.log 2)))
  refine ⟨N₀, ?_⟩
  intro N hN L hband j hj
  have hn : 2 ≤ N := by omega
  have hjI := mem_Ico.mp ((mem_boundaryBlock hn).mp hj)
  have hj1 : 1 ≤ j := by omega
  have hlogj : Real.log j ≤ Real.log 2 + Real.log N := by
    have hm := Real.log_le_log (by exact_mod_cast (show 0 < j by omega))
      (show (j : ℝ) ≤ 2 * N by exact_mod_cast (PaperP1.OrdinaryCandidateMonotonicity.boundary_lt_two_mul hn hj).le)
    rw [Real.log_mul (by norm_num) (by exact_mod_cast (show N ≠ 0 by omega))] at hm
    exact hm
  have hf : (windowLength j : ℝ) ≤ Real.log j / (4 * Real.log 2) :=
    Nat.floor_le (div_nonneg (Real.log_nonneg (by exact_mod_cast hj1)) (by positivity))
  have hψ : (windowLength j : ℝ) ≤ (Real.log N / Real.log 2 + 1) / 4 := by
    calc
      _ ≤ Real.log j / (4 * Real.log 2) := hf
      _ ≤ (Real.log 2 + Real.log N) / (4 * Real.log 2) :=
        div_le_div_of_nonneg_right hlogj (by positivity)
      _ = (Real.log N / Real.log 2 + 1) / 4 := by field_simp; ring
  have hlarge : 2 * C + 2 ≤ Real.log N / Real.log 2 :=
    (le_div_iff₀ hlog2).mpr (h₀ N (by omega))
  have hnonneg : 0 ≤ Real.log N / Real.log 2 :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))) hlog2.le
  have hlo := (abs_le.mp hband).1
  exact_mod_cast (show (windowLength j : ℝ) ≤ L by linarith only [hψ, hlarge, hnonneg, hlo])

theorem census_of_two_candidates (C a : ℝ) (ha : 0 ≤ a)
    (hTwo : TwoCandidateDensity windowLength a) : OrdinaryCensusDensity C a := by
  intro τ hτ
  obtain ⟨NE, hE⟩ := hTwo (τ / 2) (by positivity)
  obtain ⟨NW, hW⟩ := window_actual C
  refine ⟨max 2 (max NE NW), ?_⟩
  intro N hN L i hband
  have hn : 2 ≤ N := by omega
  have hs : missingCandidates N (L + i.val) ((N : ℝ) ^ a) ⊆ prefixBad windowLength a (2 * N) := by
    intro j hj
    obtain ⟨hjB, hjc⟩ := mem_filter.mp hj
    have hj2 := PaperP1.OrdinaryCandidateMonotonicity.boundary_lt_two_mul hn hjB
    have hw : windowLength j + 1 ≤ L + i.val + 1 := by
      have h := hW N (by omega) L hband j hjB
      omega
    have hq := PaperP1.OrdinaryCandidateMonotonicity.smooth_threshold hn hj2.le ha
    have hc := PaperP1.OrdinaryCandidateMonotonicity.card_le (j := j) hw hq
    exact mem_filter.mpr ⟨mem_range.mpr hj2, hc.trans_lt hjc⟩
  calc
    _ ≤ ((prefixBad windowLength a (2 * N)).card : ℝ) := by exact_mod_cast card_le_card hs
    _ ≤ (τ / 2) * ((2 * N : ℕ) : ℝ) := hE (2 * N) (by omega)
    _ = τ * N := by push_cast; ring

theorem ordinary_census_of_corollary_six (C a : ℝ) (ha : 0 < a) (hInput : CorollarySixLogInput a) :
    OrdinaryCensusDensity C a := by
  obtain ⟨ρ, hρ, hI⟩ := hInput
  exact census_of_two_candidates C a ha.le (two_candidates_of_relative windowLength window_grows a ρ hρ hI)

end PaperP1.LogarithmicOrdinaryCensusBridge
