module

public import PaperP1.Analysis.LeadingSaddleLogBounds
public import PaperP1.Analysis.SmoothReciprocalLeadingLower
public import PaperP1.Asymptotics.StratifiedReciprocalUpper

/-! # The normalized logarithmic deficits of all actual reciprocal sums tend to two

These are unconditional leading limits. The finer o(nu_N) error in the original
companion equivalent remains a distinct unresolved obligation.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ReciprocalLeadingLimits

open Filter SaddleParameters SaddleScales HardSaddleGrowth ReciprocalOddPivots DyadicOddPivots
  LeadingSaddleLogBounds

theorem uniform_normalized_bounds (ε : ℝ) (hε : 0 < ε) : ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2,
    ((2 - ε ≤ (Real.log N - Real.log (primeSum N)) / saddleCutoff 1 (Real.log N)) ∧
      ((Real.log N - Real.log (primeSum N)) / saddleCutoff 1 (Real.log N) ≤ 2 + ε)) ∧
    ((2 - ε ≤ (Real.log N - Real.log (pivotSum N)) / saddleCutoff 1 (Real.log N)) ∧
      ((Real.log N - Real.log (pivotSum N)) / saddleCutoff 1 (Real.log N) ≤ 2 + ε)) ∧
    ((2 - ε ≤ (Real.log N - Real.log (dyadicSum N)) / saddleCutoff 1 (Real.log N)) ∧
      ((Real.log N - Real.log (dyadicSum N)) / saddleCutoff 1 (Real.log N) ≤ 2 + ε)) := by
  obtain ⟨NL, hl⟩ := SmoothReciprocalLeadingLower.uniform_original_lower (2 + ε) (by linarith only [hε])
  obtain ⟨NU, hu⟩ := StratifiedReciprocalUpper.uniform_original_upper (2 - ε) (by linarith only [hε])
  obtain ⟨HB, hb⟩ := square_band_eventually
  have hlogT : Tendsto (fun N : ℕ ↦ Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨NG, hg⟩ := eventually_atTop.mp (hlogT.eventually (eventually_ge_atTop HB))
  refine ⟨max NL (max NU NG), ?_⟩
  intro N hN
  have hV := (hb (Real.log N) (hg N (by omega))).2.1
  obtain ⟨hlo, hlf, hld⟩ := hl N (by omega)
  obtain ⟨huo, huf, hud⟩ := hu N (by omega)
  exact ⟨reciprocal_log_bounds (by omega : 0 < N) hV hlo huo,
    reciprocal_log_bounds (by omega : 0 < N) hV hlf huf,
    reciprocal_log_bounds (by omega : 0 < N) hV hld hud⟩

theorem ordinary_limit :
    Tendsto (fun N : ℕ ↦ (Real.log N - Real.log (primeSum N)) / saddleCutoff 1 (Real.log N))
      atTop (nhds 2) := by
  apply limit_of_uniform_bounds
  intro ε hε
  obtain ⟨N₀, h⟩ := uniform_normalized_bounds ε hε
  exact ⟨max N₀ 2, fun N hN ↦ (h N hN).1⟩

theorem full_limit :
    Tendsto (fun N : ℕ ↦ (Real.log N - Real.log (pivotSum N)) / saddleCutoff 1 (Real.log N))
      atTop (nhds 2) := by
  apply limit_of_uniform_bounds
  intro ε hε
  obtain ⟨N₀, h⟩ := uniform_normalized_bounds ε hε
  exact ⟨max N₀ 2, fun N hN ↦ (h N hN).2.1⟩

theorem dyadic_limit :
    Tendsto (fun N : ℕ ↦ (Real.log N - Real.log (dyadicSum N)) / saddleCutoff 1 (Real.log N))
      atTop (nhds 2) := by
  apply limit_of_uniform_bounds
  intro ε hε
  obtain ⟨N₀, h⟩ := uniform_normalized_bounds ε hε
  exact ⟨max N₀ 2, fun N hN ↦ (h N hN).2.2⟩

end PaperP1.ReciprocalLeadingLimits
