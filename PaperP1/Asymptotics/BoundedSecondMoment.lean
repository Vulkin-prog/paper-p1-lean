module

public import PaperP1.Asymptotics.PairActivity
public import PaperP1.Asymptotics.CriticalActualMean
public import PaperP1.Model.FactorialCountMoments

/-! # An unconditional bounded second factorial moment of the original count -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BoundedSecondMoment

open Finset PaperP1.Model PaperP1.CountObservables PaperP1.FactorialCountMoments

def seedConstant (C : ℝ) : ℝ := (2 * (2 : ℝ) ^ C) ^ 2 + 1

theorem seedConstant_gt_one (C : ℝ) : 1 < seedConstant C := by
  have hp : 0 < 2 * (2 : ℝ) ^ C := by positivity
  unfold seedConstant
  nlinarith only [sq_pos_of_pos hp]

theorem uniform_bound (C : ℝ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      factorialCountMoment (dyadicBlock N) L 2 ≤ seedConstant C := by
  obtain ⟨NK, _hNK, hk⟩ := PairActivity.uniform_cumulant C (1 / 3) (by norm_num)
  obtain ⟨NM, _hNM, hm⟩ := CriticalActualMean.uniform_bounds C
  refine ⟨2 + NK + NM, by omega, ?_⟩
  intro N hN L hband
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hsmall : (N : ℝ) ^ (-2 / 3 + 1 / 3 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num)
  have hκ : RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L ≤ 1 :=
    (le_abs_self _).trans ((hk N (by omega) L hband (dyadicBlock N) (subset_refl _)).trans hsmall)
  have hmean := hm N (by omega) L hband
  have hmean0 : 0 ≤ countMoment (dyadicBlock N) L 1 :=
    (CriticalActualMean.lowerMean_pos C).le.trans hmean.1
  have hsquare := pow_le_pow_left₀ hmean0 hmean.2 2
  rw [factorialCountMoment_two (subset_refl (dyadicBlock N))]
  unfold RegularCumulantTransfer.secondFactorialCumulant at hκ
  unfold seedConstant
  linarith only [hκ, hsquare]

end PaperP1.BoundedSecondMoment
