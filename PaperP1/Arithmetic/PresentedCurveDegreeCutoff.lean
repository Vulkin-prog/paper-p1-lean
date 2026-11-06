module

public import PaperP1.Arithmetic.PresentedCurveQuadraticCount
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Union

/-! # A total curve-degree budget controls the actual high-degree integer-point exceptions -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PresentedCurveDegreeCutoff

open Finset
attribute [local instance] MvPolynomial.gradedAlgebra

variable {σ B : Type} [Finite σ] [CommRing B] [Algebra ℚ B]
  {H : ℕ → Submodule ℚ B} [GradedAlgebra H]

theorem cover (f : MvPolynomial.homogeneousSubmodule σ ℚ →+*ᵍ H)
    (hscalar : ∀ a : ℚ, f (algebraMap ℚ (MvPolynomial σ ℚ) a) = algebraMap ℚ B a)
    (honto : Function.Surjective f) (family : Finset (GradedProjectiveCurveData.Curve H))
    (b : ℝ) (hbudget : (∑ Γ ∈ family, (Γ.degree : ℝ)) ≤ b)
    (M N : ℕ) (hM : 0 < M) (hN : 1 ≤ N) (z : σ) (U : Finset (σ → ℤ))
    (hnormal : ∀ v ∈ U, v z = 1) (hheight : ∀ v ∈ U, ∀ i, |v i| ≤ (N : ℤ))
    (hcover : ∀ v ∈ U, ∃ Γ ∈ family, ∀ P ∈ PresentedProjectiveCurveData.coordinateIdeal f Γ,
      MvPolynomial.eval (fun i ↦ (v i : ℚ)) P = 0) :
    ∃ (T : Finset (σ → ℤ)) (low : Finset (GradedProjectiveCurveData.Curve H)),
      T ⊆ U ∧ low ⊆ family ∧ (∀ Γ ∈ low, Γ.degree ≤ (M : ℚ)) ∧ low.card ≤ family.card ∧
      (T.card : ℝ) ≤ UniformIntegralCurveCount.constant.{0} (Nat.card σ) * b ^ 2 *
        (DegreeUniformAffineParameters.logarithmicBudget N : ℝ) ^ 17 * (N : ℝ) ^ (1 / (M : ℝ)) ∧
      ∀ v ∈ U, v ∉ T → ∃ Γ ∈ low, ∀ P ∈ PresentedProjectiveCurveData.coordinateIdeal f Γ,
        MvPolynomial.eval (fun i ↦ (v i : ℚ)) P = 0 := by
  classical
  let low := family.filter (fun Γ ↦ Γ.degree ≤ (M : ℚ))
  let high := family.filter (fun Γ ↦ (M : ℚ) < Γ.degree)
  let pts := fun Γ : GradedProjectiveCurveData.Curve H ↦
    NormalizedIntegerPoints.points (PresentedProjectiveCurveData.coordinateIdeal f Γ) z N
  let T := U ∩ high.biUnion pts
  have hC := UniformIntegralCurveCount.constant_pos.{0} (Nat.card σ)
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  let K : ℝ := UniformIntegralCurveCount.constant.{0} (Nat.card σ) *
    (DegreeUniformAffineParameters.logarithmicBudget N : ℝ) ^ 17 * (N : ℝ) ^ (1 / (M : ℝ))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hpoint (Γ : GradedProjectiveCurveData.Curve H) (hΓ : Γ ∈ high) :
      ((pts Γ).card : ℝ) ≤ K * (Γ.degree : ℝ) ^ 2 := by
    have hdeg : (M : ℝ) ≤ (Γ.degree : ℝ) := by
      exact_mod_cast (mem_filter.mp hΓ).2.le
    have hrec := one_div_le_one_div_of_le hMreal hdeg
    have hr := Real.rpow_le_rpow_of_exponent_le hNreal hrec
    calc
      _ ≤ UniformIntegralCurveCount.constant.{0} (Nat.card σ) * (Γ.degree : ℝ) ^ 2 *
          (DegreeUniformAffineParameters.logarithmicBudget N : ℝ) ^ 17 *
            (N : ℝ) ^ (1 / (Γ.degree : ℝ)) :=
        PresentedCurveQuadraticCount.points_bound f hscalar honto Γ z N hN
      _ ≤ UniformIntegralCurveCount.constant.{0} (Nat.card σ) * (Γ.degree : ℝ) ^ 2 *
          (DegreeUniformAffineParameters.logarithmicBudget N : ℝ) ^ 17 *
            (N : ℝ) ^ (1 / (M : ℝ)) := mul_le_mul_of_nonneg_left hr (by positivity)
      _ = K * (Γ.degree : ℝ) ^ 2 := by dsimp [K]; ring
  have hsum0 : 0 ≤ ∑ Γ ∈ family, (Γ.degree : ℝ) :=
    sum_nonneg (fun Γ _ ↦ by exact_mod_cast Γ.degree_pos.le)
  have hsq : (∑ Γ ∈ high, (Γ.degree : ℝ) ^ 2) ≤ b ^ 2 := by
    calc
      _ ≤ ∑ Γ ∈ family, (Γ.degree : ℝ) ^ 2 :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun Γ _ _ ↦ sq_nonneg _)
      _ ≤ (∑ Γ ∈ family, (Γ.degree : ℝ)) ^ 2 :=
        sum_sq_le_sq_sum_of_nonneg (fun Γ _ ↦ by exact_mod_cast Γ.degree_pos.le)
      _ ≤ b ^ 2 := pow_le_pow_left₀ hsum0 hbudget 2
  have hcard : (T.card : ℝ) ≤ ∑ Γ ∈ high, ((pts Γ).card : ℝ) := by
    exact_mod_cast (card_le_card (inter_subset_right : T ⊆ high.biUnion pts)).trans
      (card_biUnion_le : (high.biUnion pts).card ≤ ∑ Γ ∈ high, (pts Γ).card)
  have hTbound : (T.card : ℝ) ≤ UniformIntegralCurveCount.constant.{0} (Nat.card σ) * b ^ 2 *
      (DegreeUniformAffineParameters.logarithmicBudget N : ℝ) ^ 17 * (N : ℝ) ^ (1 / (M : ℝ)) := by
    calc
      _ ≤ ∑ Γ ∈ high, ((pts Γ).card : ℝ) := hcard
      _ ≤ ∑ Γ ∈ high, K * (Γ.degree : ℝ) ^ 2 := sum_le_sum (fun Γ hΓ ↦ hpoint Γ hΓ)
      _ = K * ∑ Γ ∈ high, (Γ.degree : ℝ) ^ 2 := (mul_sum _ _ _).symm
      _ ≤ K * b ^ 2 := mul_le_mul_of_nonneg_left hsq hK
      _ = _ := by dsimp [K]; ring
  refine ⟨T, low, inter_subset_left, filter_subset _ _, ?_, card_filter_le _ _, hTbound, ?_⟩
  · intro Γ hΓ
    exact (mem_filter.mp hΓ).2
  · intro v hv hvT
    obtain ⟨Γ, hΓ, hzero⟩ := hcover v hv
    have hle : Γ.degree ≤ (M : ℚ) := by
      by_contra hn
      have hhigh : Γ ∈ high := mem_filter.mpr ⟨hΓ, lt_of_not_ge hn⟩
      have hpts : v ∈ pts Γ := by
        apply (NormalizedIntegerPoints.mem_points _ z N v).mpr
        exact ⟨⟨hheight v hv, hnormal v hv⟩, hzero⟩
      exact hvT (mem_inter.mpr ⟨hv, mem_biUnion.mpr ⟨Γ, hhigh, hpts⟩⟩)
    exact ⟨Γ, mem_filter.mpr ⟨hΓ, hle⟩, hzero⟩

end PaperP1.PresentedCurveDegreeCutoff
