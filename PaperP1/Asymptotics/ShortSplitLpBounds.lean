module

public import PaperP1.Model.SplitSumLp

/-! # The small-degree coefficient giving the actual uniform Lp bound -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ShortSplitLpBounds

open scoped ENNReal
open Finset MeasureTheory PaperP1.SplitOffsetProducts PaperP1.ShortSplitMoments PaperP1.SplitSumLp
open PaperP1.ProfileTupleCount PaperP1.Model.InfiniteRademacher

local instance : MeasurableSpace PaperP1.Arithmetic.F₂ := ⊤

theorem small_c_lpNorm (v : ℕ) (hv : 2 ≤ v) (heven : Even v) (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ a b : ℝ, 0 < a → ∀ D A₀ : ℝ,
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ W : ℕ, ∀ A : Finset ℤ,
        0 < W → Even A.card → 2 ≤ A.card → (W : ℝ) ≤ D * (Real.log N) ^ A₀ →
        (A.card : ℝ) ≤ c * Real.log (Real.log N) → (∀ a ∈ A, a.natAbs ≤ W) →
        ∀ S : Finset ℕ, (∀ n ∈ S, a * N ≤ n ∧ (n : ℝ) ≤ b * N) →
        lpNorm (sumValue A S) (v : ℝ≥0∞) infiniteRademacherMeasure ≤ (N : ℝ) ^ (1 / 2 + ε) ∧
        eLpNorm (sumValue A S) (v : ℝ≥0∞) infiniteRademacherMeasure ≤
          ENNReal.ofReal ((N : ℝ) ^ (1 / 2 + ε)) := by
  have hvr : (0 : ℝ) < v := by exact_mod_cast (show 0 < v by omega)
  have hv2 : (2 : ℝ) ≤ v := by exact_mod_cast hv
  let K := (v : ℝ) * ((v : ℝ) - 1) + 2
  have hK : 0 < K := by dsimp [K]; nlinarith only [hv2]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let c := ε * v / (2 * K * Real.log 2)
  have hc : 0 < c := by dsimp [c]; positivity
  have hcoefficient : c * K * Real.log 2 = ε * v / 2 := by
    dsimp [c]
    field_simp
  let θ := ε * v / 2
  have hθ : 0 < θ := by dsimp [θ]; positivity
  refine ⟨c, hc, ?_⟩
  intro a b ha D A₀
  obtain ⟨Np, hNp⟩ := uniform_moment_real_bounds v hv heven a b ha c D A₀ θ hc.le hθ
  refine ⟨max 2 Np, ?_⟩
  intro N hN W A hW hAeven hcard hwidth hdegree hA S hS
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hm := hNp N (by omega) W A hW hAeven hcard hwidth hdegree hA S hS
  have hmoment_nonneg : 0 ≤ ∫ ω, |sumValue A S ω| ^ v ∂infiniteRademacherMeasure :=
    integral_nonneg fun ω ↦ pow_nonneg (abs_nonneg _) _
  have hexp : (mainExponent v c + θ) * (1 / (v : ℝ)) = 1 / 2 + ε := by
    have hmain : mainExponent v c = (v : ℝ) / 2 + c * K * Real.log 2 := rfl
    rw [hmain, hcoefficient]
    dsimp [θ]
    field_simp; ring
  have hlp : lpNorm (sumValue A S) (v : ℝ≥0∞) infiniteRademacherMeasure ≤ (N : ℝ) ^ (1 / 2 + ε) := by
    rw [lpNorm_eq_moment A S v (by omega)]
    calc
      _ ≤ ((N : ℝ) ^ (mainExponent v c + θ)) ^ (1 / (v : ℝ)) :=
        Real.rpow_le_rpow hmoment_nonneg hm (by positivity)
      _ = _ := by rw [← Real.rpow_mul hn.le, hexp]
  refine ⟨hlp, ?_⟩
  rw [← ofReal_lpNorm (sumValue_memLp A S (v : ℝ≥0∞))]
  exact ENNReal.ofReal_le_ofReal hlp

end PaperP1.ShortSplitLpBounds
