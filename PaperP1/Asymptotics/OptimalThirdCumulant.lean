module

public import PaperP1.Asymptotics.SharpThirdActivity
public import PaperP1.Asymptotics.SharpThirdCumulantLower

/-! # Complete main Theorem 14.1 at the optimal 41/30 power

The lower constant depends only on the critical band. The full original
count, incompatible triples and repeated-index terms are retained.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OptimalThirdCumulant

open Finset Model ThirdRunFactorialCumulant

def lowerConstant (C : ℝ) : ℝ := 5 * ThreeSlopePositiveActivity.lowerConstant C

theorem lowerConstant_pos (C : ℝ) : 0 < lowerConstant C :=
  mul_pos (by norm_num) (ThreeSlopePositiveActivity.lower_constant_pos C)

theorem article_14_1 (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      lowerConstant C * (N : ℝ) ^ (-41 / 30 : ℝ) ≤ thirdFactorialCumulant (dyadicBlock N) L ∧
        thirdFactorialCumulant (dyadicBlock N) L ≤ (N : ℝ) ^ (-41 / 30 + ε) := by
  obtain ⟨NL, _hNL, hl⟩ := SharpThirdCumulantLower.article_14_5 C
  obtain ⟨NU, _hNU, hu⟩ := SharpThirdActivity.uniform_cumulant C ε hε
  refine ⟨4 + NL + NU, by omega, ?_⟩
  intro N hN L hband
  exact ⟨(hl N (by omega) L hband).2.2,
    (le_abs_self _).trans (hu N (by omega) L hband (dyadicBlock N) Subset.rfl)⟩

end PaperP1.OptimalThirdCumulant
