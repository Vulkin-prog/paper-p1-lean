module

public import PaperP1.Analysis.OrdinaryReciprocalPrimeInput
public import PaperP1.Asymptotics.FineReciprocalUpper

/-! # The remaining fine reciprocal obligation is one-sided

The upper direction is proved internally. The lower direction below is
an explicit ordinary theorem argument, never an axiom or proved bound.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OrdinaryReciprocalPrimeLowerInput

open Filter SaddleParameters SaddleScales HardSaddleExplicitScale OrdinaryReciprocalPrimeInput
  ReciprocalOddPivots

def LowerInput : Prop := ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2,
  (N : ℝ) * Real.exp (-2 * saddleCutoff 1 (Real.log N) - ε * saddleNu 1 (Real.log N)) ≤ primeSum N

theorem uniform_gap (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2,
      |2 * saddleCutoff 1 (Real.log N) - explicitScale (Real.log N)| ≤ ε * saddleNu 1 (Real.log N) := by
  have hlogT : Tendsto (fun N : ℕ ↦ Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hg : Tendsto (fun N : ℕ ↦
      |(2 * saddleCutoff 1 (Real.log N) - explicitScale (Real.log N)) / saddleNu 1 (Real.log N)|)
      atTop (nhds 0) := by
    simpa only [Function.comp_def, abs_zero] using tendsto_hard_saddle_gap.abs.comp hlogT
  obtain ⟨N₀, h⟩ := eventually_atTop.mp
    ((hg.eventually (eventually_lt_nhds hε)).and
      (hlogT.eventually (eventually_ge_atTop (max (saddleThreshold 1) 1))))
  refine ⟨N₀, ?_⟩
  intro N hN
  obtain ⟨he, hroot⟩ := h N (by omega)
  have hH : 0 < Real.log N := by have := (le_max_right _ _).trans hroot; linarith only [this]
  have hV := saddleCutoff_pos (by norm_num : (0 : ℝ) < 1) ((le_max_left _ _).trans hroot)
  have hν : 0 < saddleNu 1 (Real.log N) := div_pos hH hV
  rw [abs_div, abs_of_pos hν] at he
  exact (div_le_iff₀ hν).mp he.le

theorem uniform_explicit_upper (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2,
      primeSum N ≤ (N : ℝ) * Real.exp (-explicitScale (Real.log N) + ε * saddleNu 1 (Real.log N)) := by
  obtain ⟨NU, hu⟩ := FineReciprocalUpper.uniform_original_upper (ε / 2) (by positivity)
  obtain ⟨NG, hg⟩ := uniform_gap (ε / 2) (by positivity)
  refine ⟨max NU NG, ?_⟩
  intro N hN
  obtain ⟨hl, _hh⟩ := abs_le.mp (hg N (by omega))
  exact (hu N (by omega)).1.trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (by linarith only [hl])) (Nat.cast_nonneg N))

theorem eipInput_of_lower (hLower : LowerInput) : EIPInput := by
  intro ε hε
  obtain ⟨NU, hu⟩ := uniform_explicit_upper ε hε
  obtain ⟨NL, hl⟩ := hLower (ε / 2) (by positivity)
  obtain ⟨NG, hg⟩ := uniform_gap (ε / 2) (by positivity)
  refine ⟨max NU (max NL NG), ?_⟩
  intro N hN
  obtain ⟨_hlo, hhi⟩ := abs_le.mp (hg N (by omega))
  refine ⟨?_, hu N (by omega)⟩
  exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hhi]))
    (Nat.cast_nonneg N)).trans (hl N (by omega))

theorem lower_of_eipInput (hinput : EIPInput) : LowerInput := by
  intro ε hε
  obtain ⟨NI, hi⟩ := hinput (ε / 2) (by positivity)
  obtain ⟨NG, hg⟩ := uniform_gap (ε / 2) (by positivity)
  refine ⟨max NI NG, ?_⟩
  intro N hN
  obtain ⟨hlo, _hhi⟩ := abs_le.mp (hg N (by omega))
  exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hlo]))
    (Nat.cast_nonneg N)).trans (hi N (by omega)).1

theorem eipInput_iff_lower : EIPInput ↔ LowerInput :=
  ⟨lower_of_eipInput, eipInput_of_lower⟩

end PaperP1.OrdinaryReciprocalPrimeLowerInput
