module

public import PaperP1.Asymptotics.FixedQuadraticFactorialMoments
public import PaperP1.Model.TouchardApproximation

/-! # Exact ordinary fixed moment correction through the Poisson Touchard polynomial, with remainder exponent1 -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedQuadraticOrdinaryMoments

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.FactorialCountMoments
  PaperP1.CountObservables PaperP1.HeterogeneousDirectMaximum PaperP1.TouchardCountMoments

theorem uniform_fixed (r : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        |countMoment G L r - (touchard r).eval (actualMean G L) -
          RegularCumulantTransfer.secondFactorialCumulant G L / 2 *
            ((touchard r).derivative.derivative).eval (actualMean G L)| ≤ (N : ℝ) ^ (-1 + ε) := by
  classical
  have hper (i : Fin (r + 1)) := FixedQuadraticFactorialMoments.uniform_fixed (max 2 i.val) (le_max_left _ _)
    C (ε / 2) (by positivity)
  choose NJ _hNJ hj using hper
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption
    (∑ j ∈ range (r + 1), (Nat.stirlingSecond r j : ℝ)) (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨10 + NF + univ.sup NJ, by omega, ?_⟩
  intro N hN L hband G hG
  let T := (N : ℝ) ^ (-1 + ε / 2)
  have hT : 0 ≤ T := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have herror (j : ℕ) (hjrange : j ∈ range (r + 1)) :
      |factorialCountMoment G L j - actualMean G L ^ j -
        (j.choose 2 : ℝ) * actualMean G L ^ (j - 2) * RegularCumulantTransfer.secondFactorialCumulant G L| ≤ T := by
    by_cases hjtwo : 2 ≤ j
    · let i : Fin (r + 1) := ⟨j, mem_range.mp hjrange⟩
      have hNi : NJ i ≤ univ.sup NJ := le_sup (f := NJ) (mem_univ i)
      have h := hj i N (by omega) L hband G hG
      simpa only [i, max_eq_right hjtwo] using h
    · have hsmall : j = 0 ∨ j = 1 := by omega
      rcases hsmall with rfl | rfl
      · have hzero : factorialCountMoment G L 0 = 1 := by
          rw [factorialCountMoment_eq_subset hG 0]
          simp only [Nat.factorial_zero, Nat.cast_one, powersetCard_zero, sum_singleton, infiniteJointMoment_empty, mul_one]
        simpa only [hzero, pow_zero, Nat.choose_eq_zero_of_lt (by decide : 0 < 2), Nat.cast_zero,
          zero_mul, sub_self, sub_zero, abs_zero] using hT
      · have hone : factorialCountMoment G L 1 = actualMean G L := by
          rw [factorialCountMoment_one, countMoment_one hG]
          rfl
        simpa only [hone, pow_one, Nat.choose_eq_zero_of_lt (by decide : 1 < 2), Nat.cast_zero,
          zero_mul, sub_self, sub_zero, abs_zero] using hT
  have hfinite := TouchardApproximation.finite_bound r (factorialCountMoment G L) (actualMean G L)
    (RegularCumulantTransfer.secondFactorialCumulant G L) T herror
  rw [← ordinary_eq_factorial hG r] at hfinite
  exact hfinite.trans (by
    convert hf N (by omega) using 1
    congr 1
    ring)

end PaperP1.FixedQuadraticOrdinaryMoments
