module

public import PaperP1.Model.RetainedModifiedMomentDecomposition
public import PaperP1.Algebra.ShiftedBinomialGenerator
public import PaperP1.Model.SecondFactorialCorrection

/-! # Exact finite weighted pair-moment generators and their positive exceptional-event subseries -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RetainedPairMomentGenerator

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.CountObservables PaperP1.RegularStarts
  PaperP1.RetainedActiveSubsetMoments PaperP1.RetainedModifiedMomentDecomposition PaperP1.RetainedReferenceTheorem

def meanSum (u H : ℝ) (N L : ℕ) : ℝ :=
  ∑ r ∈ range ((regularStarts N L).card + 1), u ^ r * pairMean H N L r

def leakageSum (u H : ℝ) (N L : ℕ) : ℝ :=
  ∑ r ∈ range ((regularStarts N L).card + 1), u ^ r * pairLeakage H N L r

theorem beta_nonneg (H : ℝ) (N L : ℕ) : 0 ≤ beta H N L :=
  sum_nonneg fun e _he ↦ infiniteJointMoment_nonneg L e

theorem leakageSum_eq_tsum (u H : ℝ) (N L : ℕ) :
    leakageSum u H N L = ∑' r : ℕ, u ^ r * pairLeakage H N L r := by
  symm
  apply tsum_eq_sum
  intro r hr
  have hlarge : (regularStarts N L).card < r := by simp only [mem_range, not_lt] at hr; omega
  rw [pairLeakage_zero_large H N L r hlarge, mul_zero]

theorem leakage_le_mean (u H : ℝ) (N L : ℕ) (hu : 0 ≤ u) : leakageSum u H N L ≤ meanSum u H N L :=
  sum_le_sum fun r _hr ↦ mul_le_mul_of_nonneg_left (pairLeakage_le_mean H N L r) (pow_nonneg hu _)

theorem mean_bound {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (H u : ℝ) (hu : 0 ≤ u)
    (hn : 2 ≤ (regularStarts N L).card) :
    meanSum u H N L ≤ u ^ 2 * beta H N L * (1 + u * (2 ^ L : ℝ)⁻¹) ^ ((regularStarts N L).card - 2) := by
  calc
    _ ≤ ∑ r ∈ range ((regularStarts N L).card + 1), u ^ r * pairBinomialTerm H N L r := by
      apply sum_le_sum
      intro r _hr
      rw [pair_mean hN hL]
      exact mul_le_mul_of_nonneg_left (sub_le_self _ (RetainedCardinalityDeficits.secondCoefficient_nonneg H N L r)) (pow_nonneg hu _)
    _ = _ := ShiftedBinomialGenerator.finite_sum _ hn u _ _

theorem exponential_bound {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (H u : ℝ) (hu : 0 ≤ u)
    (hn : 2 ≤ (regularStarts N L).card) :
    meanSum u H N L ≤ u ^ 2 * beta H N L * Real.exp (u * countMoment (regularStarts N L) L 1) := by
  let p : ℝ := (2 ^ L : ℝ)⁻¹
  let n := (regularStarts N L).card
  have hpow : (1 + u * p) ^ (n - 2) ≤ Real.exp (u * countMoment (regularStarts N L) L 1) := by
    calc
      _ ≤ (Real.exp (u * p)) ^ (n - 2) := pow_le_pow_left₀ (by positivity)
        (by linarith only [Real.add_one_le_exp (u * p)]) _
      _ = Real.exp ((n - 2 : ℕ) * (u * p)) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        rw [SecondFactorialCorrection.regular_mean hN hL]
        have hcard : ((n - 2 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 2
        have h := mul_le_mul_of_nonneg_right hcard (mul_nonneg hu (by positivity : 0 ≤ p))
        convert h using 1; dsimp only [n, p]; ring
  exact (mean_bound hN hL H u hu hn).trans (mul_le_mul_of_nonneg_left hpow
    (mul_nonneg (pow_nonneg hu _) (beta_nonneg H N L)))

end PaperP1.RetainedPairMomentGenerator
