module

public import PaperP1.Asymptotics.PairActivity
public import PaperP1.Probability.HermiteSignedComparison
public import PaperP1.Probability.SignedAtomicDistance

/-! # Optimal power for the difference of the actual Hermite and quadratic references

Every estimate is supplied by the internal actual pair theorem. The
second factorial cumulant, including its repeated-index term, is the original
one on every dyadic subground. The reference mean may be any nonnegative mean.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ActualHermiteReferenceRate

open Finset PaperP1.Model

theorem uniform_comparison (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        ∀ μ : ℝ, 0 ≤ μ →
        SignedAtomicDistance.distance
          (QuadraticPoisson.reference μ (RegularCumulantTransfer.secondFactorialCumulant G L))
          (CompletedLaw.toSignedMeasure (HermiteReference.reference μ
            (RegularCumulantTransfer.secondFactorialCumulant G L))) ≤ (N : ℝ) ^ (-4 / 3 + ε) := by
  let η := min (ε / 4) (1 / 12)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hηε : η ≤ ε / 4 := min_le_left _ _
  have hηcap : η ≤ 1 / 12 := min_le_right _ _
  obtain ⟨NP, _hNP, hp⟩ := PairActivity.uniform_cumulant C η hη
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (4 * Real.exp 2) (-4 / 3 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 10 (max NP NF), by omega, ?_⟩
  intro N hN L hband G hG μ hμ
  let α := RegularCumulantTransfer.secondFactorialCumulant G L
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hα : |α| ≤ (N : ℝ) ^ (-2 / 3 + η) := hp N (by omega) L hband G hG
  have hα1 : |α| ≤ 1 := hα.trans (Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith only [hηcap]))
  have hsq : α ^ 2 ≤ (N : ℝ) ^ (-4 / 3 + ε / 2) := by
    calc
      _ = |α| ^ 2 := (sq_abs α).symm
      _ ≤ ((N : ℝ) ^ (-2 / 3 + η)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hα 2
      _ = (N : ℝ) ^ ((-2 / 3 + η) * 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]
        norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hηε])
  have he := HermiteSignedComparison.actual_signed_error_symmetric μ α hμ
  change SignedAtomicDistance.distance (QuadraticPoisson.reference μ α)
    (CompletedLaw.toSignedMeasure (HermiteReference.reference μ α)) ≤ _ at he
  calc
    _ ≤ 4 * α ^ 2 * Real.exp (2 * |α|) := he
    _ ≤ (4 * Real.exp 2) * (N : ℝ) ^ (-4 / 3 + ε / 2) := by
      have hexp := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hα1 (by norm_num : (0 : ℝ) ≤ 2))
      have hm := mul_le_mul hsq hexp (Real.exp_nonneg _) (Real.rpow_nonneg hn.le _)
      nlinarith only [hm]
    _ ≤ (N : ℝ) ^ ((-4 / 3 + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.ActualHermiteReferenceRate
