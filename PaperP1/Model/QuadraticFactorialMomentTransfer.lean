module

public import PaperP1.Model.OriginalLawPolynomialMoments
public import PaperP1.Probability.FourthCharlierReference

/-! # Exact quadratic factorial moments and transfer from a polynomially weighted error -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.QuadraticFactorialMomentTransfer

open Finset PaperP1.Model PaperP1.CountObservables PaperP1.FactorialCountMoments
  PaperP1.AtomicProbability PaperP1.PoissonSequence

def referenceMoment (μ α : ℝ) (r : ℕ) : ℝ := μ ^ r + (r.choose 2 : ℝ) * μ ^ (r - 2) * α

theorem quadratic_hasSum (μ α : ℝ) (hμ : 0 ≤ μ) (r : ℕ) :
    HasSum (fun k : ℕ ↦ quadraticMass μ α k * (k.descFactorial r : ℝ))
      (referenceMoment μ α r) := by
  rcases r with _ | _ | j
  · simpa only [Nat.descFactorial_zero, Nat.cast_one, mul_one, referenceMoment,
      pow_zero, Nat.choose_eq_zero_of_lt (by omega : 0 < 2), Nat.cast_zero,
      zero_mul, add_zero] using hasSum_quadraticMass μ α hμ
  · simpa only [Nat.zero_add, Nat.descFactorial_one, referenceMoment, pow_one,
      Nat.choose_eq_zero_of_lt (by omega : 1 < 2), Nat.cast_zero, zero_mul, add_zero] using
      FourthCharlierReference.quadratic_first μ α hμ
  · have hh := FourthCharlierReference.quadratic_factorial_succ_succ μ α hμ j
    convert hh using 1
    dsimp only [referenceMoment]
    rw [Nat.cast_choose_two]
    push_cast
    ring

theorem finite_bound {N L : ℕ} {G : Finset ℕ} (hG : G ⊆ dyadicBlock N) (r : ℕ)
    (hs : Summable (fun k : ℕ ↦ (1 + (k : ℝ)) ^ r *
      |realMass (RetainedModifiedLaw.originalLaw G L) k -
        quadraticMass (countMoment G L 1) (RegularCumulantTransfer.secondFactorialCumulant G L) k|)) :
    |factorialCountMoment G L r -
      referenceMoment (countMoment G L 1) (RegularCumulantTransfer.secondFactorialCumulant G L) r| ≤
      ∑' k : ℕ, (1 + (k : ℝ)) ^ r *
        |realMass (RetainedModifiedLaw.originalLaw G L) k -
          quadraticMass (countMoment G L 1) (RegularCumulantTransfer.secondFactorialCumulant G L) k| := by
  have hμ : 0 ≤ countMoment G L 1 := by
    rw [← HeterogeneousDirectMaximum.actualMean_eq_countMoment hG]
    exact sum_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L
  have hh := (OriginalLawPolynomialMoments.factorial_hasSum G L r).sub
    (quadratic_hasSum (countMoment G L 1) (RegularCumulantTransfer.secondFactorialCumulant G L) hμ r)
  have hp (k : ℕ) : (k.descFactorial r : ℝ) ≤ (1 + (k : ℝ)) ^ r := by
    calc
      _ ≤ (k : ℝ) ^ r := by exact_mod_cast Nat.descFactorial_le_pow k r
      _ ≤ _ := pow_le_pow_left₀ (Nat.cast_nonneg k) (by linarith) r
  have hd (k : ℕ) :
      |realMass (RetainedModifiedLaw.originalLaw G L) k * (k.descFactorial r : ℝ) -
        quadraticMass (countMoment G L 1) (RegularCumulantTransfer.secondFactorialCumulant G L) k *
          (k.descFactorial r : ℝ)| ≤ (1 + (k : ℝ)) ^ r *
        |realMass (RetainedModifiedLaw.originalLaw G L) k -
          quadraticMass (countMoment G L 1) (RegularCumulantTransfer.secondFactorialCumulant G L) k| := by
    have hn : (0 : ℝ) ≤ (k.descFactorial r : ℝ) := Nat.cast_nonneg _
    rw [← sub_mul, abs_mul, abs_of_nonneg hn, mul_comm]
    exact mul_le_mul_of_nonneg_right (hp k) (abs_nonneg _)
  rw [← hh.tsum_eq]
  have ht := norm_tsum_le_tsum_norm hh.summable.norm
  simp only [Real.norm_eq_abs] at ht
  exact ht.trans (hh.summable.abs.tsum_le_tsum hd hs)

theorem exact_small_orders {N L : ℕ} {G : Finset ℕ} (hG : G ⊆ dyadicBlock N) :
    factorialCountMoment G L 0 = 1 ∧
      factorialCountMoment G L 1 = countMoment G L 1 ∧
      factorialCountMoment G L 2 = (countMoment G L 1) ^ 2 +
        RegularCumulantTransfer.secondFactorialCumulant G L := by
  refine ⟨?_, factorialCountMoment_one G L, ?_⟩
  · have hh := OriginalLawPolynomialMoments.factorial_hasSum G L 0
    simp only [Nat.descFactorial_zero, Nat.cast_one, mul_one] at hh
    exact hh.unique (hasSum_realMass _)
  · rw [factorialCountMoment_two hG, RegularCumulantTransfer.secondFactorialCumulant]
    ring

end PaperP1.QuadraticFactorialMomentTransfer
