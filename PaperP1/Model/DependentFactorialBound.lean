module

public import PaperP1.Model.DependentFamilySeeds
public import PaperP1.Model.FactorialCountMoments
public import PaperP1.Algebra.ElementarySymmetricBound

/-! # Actual factorial moments are bounded by their heterogeneous mean and dependent mass -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DependentFactorialBound

open Finset PaperP1.Algebra PaperP1.Probability PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.CountObservables PaperP1.FactorialCountMoments PaperP1.HeterogeneousDirectMaximum
  PaperP1.DependentFamilySeeds

local instance dependentFactorialBoundDecidable (P : Prop) : Decidable P := Classical.propDecidable P

theorem factorial_upper {N L : ℕ} {G : Finset ℕ} (hG : G ⊆ dyadicBlock N)
    (hL : 0 < L) (r : ℕ) :
    factorialCountMoment G L r ≤ actualMean G L ^ r + (r.factorial : ℝ) * dependentMass G L r := by
  have hsum : (∑ I ∈ G.powersetCard r, infiniteJointMoment L I) ≤
      SubsetPowerSums.elementary (fun x ↦ infiniteMarginal x L) G r + dependentMass G L r := by
    calc
      _ ≤ ∑ I ∈ G.powersetCard r, ((∏ x ∈ I, infiniteMarginal x L) +
          if 0 < runRelativeNullity L I then infiniteJointMoment L I else 0) := by
        apply sum_le_sum
        intro I _
        by_cases hz : runRelativeNullity L I = 0
        · rw [direct_joint_factor L hL I hz, hz]
          simp only [lt_self_iff_false, ite_false, add_zero, le_refl]
        · rw [ite_eq_left (Nat.pos_of_ne_zero hz)]
          exact le_add_of_nonneg_left (prod_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)
      _ = _ := by rw [sum_add_distrib, ← sum_filter]; rfl
  rw [factorialCountMoment_eq_subset hG]
  calc
    _ ≤ (r.factorial : ℝ) * (SubsetPowerSums.elementary (fun x ↦ infiniteMarginal x L) G r + dependentMass G L r) :=
      mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)
    _ = (r.factorial : ℝ) * SubsetPowerSums.elementary (fun x ↦ infiniteMarginal x L) G r +
        (r.factorial : ℝ) * dependentMass G L r := by ring
    _ ≤ _ := add_le_add
      (ElementarySymmetricBound.factorial_elementary_le (fun x ↦ infiniteMarginal x L)
        (fun x ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L) G r) le_rfl

theorem nat_power_le_factorial (n r : ℕ) :
    n ^ r ≤ (2 * r) ^ r + 2 ^ r * n.descFactorial r := by
  by_cases hn : n ≤ 2 * r
  · exact (Nat.pow_le_pow_left hn r).trans (Nat.le_add_right _ _)
  · have hbase : n ≤ 2 * (n + 1 - r) := by omega
    calc
      _ ≤ (2 * (n + 1 - r)) ^ r := Nat.pow_le_pow_left hbase r
      _ = 2 ^ r * (n + 1 - r) ^ r := Nat.mul_pow _ _ _
      _ ≤ 2 ^ r * n.descFactorial r := Nat.mul_le_mul_left _ (Nat.pow_sub_le_descFactorial n r)
      _ ≤ _ := Nat.le_add_left _ _

theorem ordinary_upper {N L : ℕ} {G : Finset ℕ} (hG : G ⊆ dyadicBlock N) (r : ℕ) :
    countMoment G L r ≤ (((2 * r) ^ r : ℕ) : ℝ) + (2 : ℝ) ^ r * factorialCountMoment G L r := by
  rw [countMoment_eq_finite hG, factorialCountMoment_eq_finite hG]
  have h := finiteExpectation_mono (cylinderProbability (dyadicCutoff N L)) (fun σ ↦
    (show ((indicatorCount G (fun x ↦ startIndicator x L) σ : ℝ) ^ r) ≤
        (((2 * r) ^ r : ℕ) : ℝ) + (2 : ℝ) ^ r *
          ((indicatorCount G (fun x ↦ startIndicator x L) σ).descFactorial r : ℝ) by
      exact_mod_cast nat_power_le_factorial (indicatorCount G (fun x ↦ startIndicator x L) σ) r))
  rw [finiteExpectation_add, finiteExpectation_const, finiteExpectation_const_mul] at h
  simpa only [FiniteProbability.total_weight, one_mul] using h

end PaperP1.DependentFactorialBound
