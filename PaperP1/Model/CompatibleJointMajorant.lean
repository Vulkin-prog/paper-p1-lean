module

public import PaperP1.Model.CompatibleNullityBound
public import PaperP1.Model.PrimitiveWindowMass

/-! # Actual joint probabilities have the exact compatible-nullity rank majorant, including incompatible and zero-marginal systems -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CompatibleJointMajorant

open Finset PaperP1.Model.InfiniteStarts

theorem pointwise (L : ℕ) (hL : 0 < L) (I : Finset ℕ) :
    infiniteJointMoment L I ≤ (∏ x ∈ I, infiniteMarginal x L) * (2 ^ runCompatibleNullity L I : ℝ) := by
  by_cases hq : 0 < infiniteJointMoment L I
  · have h := infiniteJointMoment_exact_of_pos (I.sup fun x ↦ x + L) L I hL
      (fun x hx ↦ le_sup (f := fun x ↦ x + L) hx) hq
    change infiniteJointMoment L I = (∏ x ∈ I, infiniteMarginal x L) * (2 ^ runRelativeNullity L I : ℝ) at h
    rw [← runCompatibleNullity_eq_of_positive_joint L I hq] at h
    exact h.le
  · exact (le_of_not_gt hq).trans (mul_nonneg
      (prod_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L) (by positivity))

theorem weighted_bound (F : Finset (Finset ℕ)) (L : ℕ) (hL : 0 < L) (u K : ℝ) (hu : 0 ≤ u)
    (hK : ∀ I ∈ F, (2 ^ runCompatibleNullity L I : ℝ) ≤ K) :
    (∑ I ∈ F, u ^ I.card * infiniteJointMoment L I) ≤ K * ∑ I ∈ F, ∏ x ∈ I, u * infiniteMarginal x L := by
  rw [mul_sum]
  apply sum_le_sum
  intro I hI
  have hprod : 0 ≤ u ^ I.card * ∏ x ∈ I, infiniteMarginal x L :=
    mul_nonneg (pow_nonneg hu _) (prod_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)
  calc
    _ ≤ u ^ I.card * ((∏ x ∈ I, infiniteMarginal x L) * (2 ^ runCompatibleNullity L I : ℝ)) :=
      mul_le_mul_of_nonneg_left (pointwise L hL I) (pow_nonneg hu _)
    _ = (u ^ I.card * ∏ x ∈ I, infiniteMarginal x L) * (2 ^ runCompatibleNullity L I : ℝ) := by ring
    _ ≤ (u ^ I.card * ∏ x ∈ I, infiniteMarginal x L) * K := mul_le_mul_of_nonneg_left (hK I hI) hprod
    _ = _ := by rw [prod_mul_distrib, prod_const]; ring

end PaperP1.CompatibleJointMajorant
