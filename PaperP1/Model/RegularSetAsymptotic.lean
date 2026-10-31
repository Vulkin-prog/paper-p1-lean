module

public import PaperP1.Model.RegularSetFinite

/-! # Uniform regular-set estimates in the manuscript's critical band

All thresholds precede N, the run length, deterministic subsets and affine
targets. The exceptional count is an explicit N^ε bound for every ε > 0.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RegularSetAsymptotic

open Filter MeasureTheory PaperP1.Arithmetic PaperP1.Affine PaperP1.Model
open PaperP1.Probability RegularStarts RegularAffineBounds CountObservables RegularSetFinite
open WindowRelationCode Finset

local instance regularSetAsymptoticPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
local instance regularSetAsymptoticMeasurableF2 : MeasurableSpace F₂ := ⊤

theorem critical_band_logarithmic_width (C : ℝ) :
    ∃ E : ℝ, 0 ≤ E ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ((L + 1 : ℕ) : ℝ) ≤ E * Real.log N := by
  let E : ℝ := 1 / Real.log 2 + 1
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    (PrimeLogBudget.log_nat_tendsto_atTop.eventually (eventually_ge_atTop (C + 1)))
  refine ⟨E, hE, N₀, ?_⟩
  intro N hN L hband
  have hwidth := (abs_le.mp hband).2
  have hlarge := hN₀ N hN
  have heq : Real.log N / Real.log 2 = (1 / Real.log 2) * Real.log N := by ring
  rw [heq] at hwidth
  dsimp [E]
  simp only [Nat.cast_add, Nat.cast_one]
  nlinarith

theorem dyadic_critical_relation_rank_le_one (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ x ∈ dyadicBlock N,
        Module.finrank F₂ (windowRelationCode (x - 1) (L + 1)) ≤ 1 := by
  obtain ⟨N₁, hN₁⟩ := LocalRigidityRegimes.critical_band_relation_rank_le_one
    (1 / 2 : ℝ) C (by norm_num)
  refine ⟨max 2 N₁, ?_⟩
  intro N hN L hband x hx
  have hxlo := (mem_Ico.mp hx).1
  have hbaseNat : N ≤ 2 * (x - 1) := by omega
  have hbase : (1 / 2 : ℝ) * N ≤ ((x - 1 : ℕ) : ℝ) := by
    have h : (N : ℝ) ≤ 2 * ((x - 1 : ℕ) : ℝ) := by exact_mod_cast hbaseNat
    linarith
  exact hN₁ N (by omega) (x - 1) L hbase hband

theorem irregular_count_critical (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ((irregularStarts N L).card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨E, hE, Nwidth, hwidth⟩ := critical_band_logarithmic_width C
  obtain ⟨Ncount, hcount⟩ := card_irregularStarts_le_rpow_eventually E hE ε hε
  refine ⟨max Nwidth Ncount, ?_⟩
  intro N hN L hband
  exact hcount N (by omega) L (hwidth N (by omega) L hband)

theorem affine_marginal_sum_critical (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, 0 < L →
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ A : Finset ℕ, A ⊆ dyadicBlock N → ∀ b : ℕ → Fin L → F₂,
        (∑ x ∈ A, |affineWindowMass x L (b x) - (2 ^ L : ℝ)⁻¹|) ≤
          (2 ^ L : ℝ)⁻¹ * (N : ℝ) ^ ε := by
  obtain ⟨Nrank, hrank⟩ := dyadic_critical_relation_rank_le_one C
  obtain ⟨Ncount, hcount⟩ := irregular_count_critical C ε hε
  refine ⟨max 2 (max Nrank Ncount), ?_⟩
  intro N hN L hL hband A hA b
  have hr := hrank N (by omega) L hband
  have hc := hcount N (by omega) L hband
  exact (sum_affine_deviations_le (by omega) hL hr A hA b).trans
    (mul_le_mul_of_nonneg_left hc (by positivity))

theorem nominal_times_rpow_bound {N L : ℕ} {C ε : ℝ} (hN : 2 ≤ N)
    (hband : |(L : ℝ) - Real.log N / Real.log 2| ≤ C) :
    (2 ^ L : ℝ)⁻¹ * (N : ℝ) ^ ε ≤ (2 : ℝ) ^ C * (N : ℝ) ^ (-1 + ε) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hnom := LocalRigidityConsequences.nominal_marginal_bound hN hband
  calc
    _ ≤ ((2 : ℝ) ^ C / N) * (N : ℝ) ^ ε :=
      mul_le_mul_of_nonneg_right hnom (Real.rpow_nonneg hn.le _)
    _ = _ := by
      rw [show -1 + ε = ε - 1 by ring, Real.rpow_sub hn, Real.rpow_one]
      ring

theorem regular_set_transfer (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, 0 < L →
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      lawTotalVariation (dyadicCountLaw N L) (restrictedCountLaw N L (regularStarts N L)) +
        |countMoment (dyadicBlock N) L 1 - N * (2 ^ L : ℝ)⁻¹| +
        |countMoment (regularStarts N L) L 1 - N * (2 ^ L : ℝ)⁻¹| ≤
          (4 * (2 : ℝ) ^ C) * (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨Nrank, hrank⟩ := dyadic_critical_relation_rank_le_one C
  obtain ⟨Ncount, hcount⟩ := irregular_count_critical C ε hε
  refine ⟨max 2 (max Nrank Ncount), ?_⟩
  intro N hN L hL hband
  have hNtwo : 2 ≤ N := by omega
  have hr := hrank N (by omega) L hband
  have hc := hcount N (by omega) L hband
  calc
    _ ≤ 4 * (2 ^ L : ℝ)⁻¹ * (irregularStarts N L).card :=
      regular_set_finite_transfer hNtwo hL hr
    _ ≤ 4 * ((2 ^ L : ℝ)⁻¹ * (N : ℝ) ^ ε) := by
      nlinarith [mul_le_mul_of_nonneg_left hc
        (show 0 ≤ (2 ^ L : ℝ)⁻¹ by positivity)]
    _ ≤ 4 * ((2 : ℝ) ^ C * (N : ℝ) ^ (-1 + ε)) :=
      mul_le_mul_of_nonneg_left (nominal_times_rpow_bound hNtwo hband) (by norm_num)
    _ = _ := by ring

theorem discarded_activity_critical (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, 0 < L →
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      countDisagreement (dyadicBlock N) (regularStarts N L) L ≤
        (2 * (2 : ℝ) ^ C) * (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨Nrank, hrank⟩ := dyadic_critical_relation_rank_le_one C
  obtain ⟨Ncount, hcount⟩ := irregular_count_critical C ε hε
  refine ⟨max 2 (max Nrank Ncount), ?_⟩
  intro N hN L hL hband
  have hNtwo : 2 ≤ N := by omega
  have hr := hrank N (by omega) L hband
  have hc := hcount N (by omega) L hband
  calc
    _ ≤ 2 * (2 ^ L : ℝ)⁻¹ * (irregularStarts N L).card :=
      discarded_activity_le hNtwo hL hr
    _ ≤ 2 * ((2 ^ L : ℝ)⁻¹ * (N : ℝ) ^ ε) := by
      nlinarith [mul_le_mul_of_nonneg_left hc
        (show 0 ≤ (2 ^ L : ℝ)⁻¹ by positivity)]
    _ ≤ 2 * ((2 : ℝ) ^ C * (N : ℝ) ^ (-1 + ε)) :=
      mul_le_mul_of_nonneg_left (nominal_times_rpow_bound hNtwo hband) (by norm_num)
    _ = _ := by ring

end PaperP1.RegularSetAsymptotic
