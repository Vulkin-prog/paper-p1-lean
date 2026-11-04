module

public import PaperP1.Asymptotics.CriticalBandScale
public import PaperP1.Analysis.HardSaddleGrowth
public import Mathlib.Algebra.Order.Floor.Semiring

/-! # The prescribed excess cutoff E=ceil(3V/log2) remains sublogarithmic -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SignedSaddleExcess

open Filter PaperP1.SaddleParameters PaperP1.SaddleScales PaperP1.HardSaddleGrowth

def excess (N : ℕ) : ℕ := ⌈3 * saddleCutoff 1 (Real.log N) / Real.log 2⌉₊

def widthConstant : ℝ := PaperP1.CriticalBandScale.upperScale + 1

theorem widthConstant_pos : 0 < widthConstant := by
  unfold widthConstant
  linarith only [PaperP1.CriticalBandScale.upperScale_pos]

theorem uniform_small (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ((excess N + 1 : ℕ) : ℝ) ≤ η * Real.log N := by
  have ht' : Tendsto (fun H : ℝ ↦ (3 / Real.log 2) * (saddleCutoff 1 H / H) + 2 / H)
      atTop (nhds 0) := by
    have hc : Tendsto (fun H : ℝ ↦ 2 / H) atTop (nhds 0) := tendsto_const_nhds.div_atTop tendsto_id
    simpa only [mul_zero, add_zero] using (tendsto_cutoff_div_height.const_mul (3 / Real.log 2)).add hc
  have ht : Tendsto (fun H : ℝ ↦ (3 * saddleCutoff 1 H / Real.log 2 + 2) / H)
      atTop (nhds 0) := by
    apply ht'.congr
    intro H
    ring
  have hnlog : Tendsto (fun N : ℕ ↦ Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N₀, h⟩ := eventually_atTop.mp
    ((hnlog.eventually (eventually_ge_atTop (max (saddleThreshold 1) 1))).and
      ((ht.comp hnlog).eventually (eventually_lt_nhds hη)))
  refine ⟨N₀, ?_⟩
  intro N hN
  obtain ⟨hdom, he⟩ := h N (by omega)
  have hH : 0 < Real.log N := by have := (le_max_right _ _).trans hdom; linarith
  have hv : 0 < saddleCutoff 1 (Real.log N) := saddleCutoff_pos (by norm_num) (by order)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hceil := Nat.ceil_lt_add_one (by positivity : 0 ≤ 3 * saddleCutoff 1 (Real.log N) / Real.log 2)
  change ((excess N : ℕ) : ℝ) < 3 * saddleCutoff 1 (Real.log N) / Real.log 2 + 1 at hceil
  change (3 * saddleCutoff 1 (Real.log N) / Real.log 2 + 2) / Real.log N < η at he
  have hm := (div_le_iff₀ hH).mp he.le
  push_cast
  linarith only [hceil, hm]

theorem uniform_width (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ((L + excess N + 2 : ℕ) : ℝ) ≤ widthConstant * Real.log N := by
  obtain ⟨NE, hE⟩ := uniform_small 1 (by norm_num)
  obtain ⟨NL, hL⟩ := PaperP1.CriticalBandScale.critical_band_scale C
  refine ⟨max NE NL, ?_⟩
  intro N hN L hcrit
  have he := hE N (by omega)
  have hl := (hL N (by omega) L hcrit).2
  unfold widthConstant
  push_cast at he hl ⊢
  nlinarith only [he, hl]

end PaperP1.SignedSaddleExcess
