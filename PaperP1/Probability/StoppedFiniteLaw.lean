module

public import PaperP1.Algebra.StoppedExpansion
public import PaperP1.Probability.L1Norm

/-!
# Positive stopped remainder kernels on finite probability spaces

The suffix remains inside an actual weighted count law. Its coefficients are
nonnegative and its mass is the joint activation probability of the prefix.
The unweighted ℓ¹ bound consequently has no factor exponential in the suffix.
-/

@[expose] public noncomputable section

open scoped BigOperators
open PaperP1.Algebra

namespace PaperP1.Probability

variable {Ω ι : Type*} [Fintype Ω] [LinearOrder ι]

def finiteJointMoment (P : FiniteProbability Ω) (J : ι → Ω → Bool) (I : Finset ι) : ℝ :=
  finiteExpectation P.weight (fun ω => ∏ x ∈ I, indicatorValue (J x ω))

def retainedCountReference (G : Finset ι) (D : Finset ι → Prop)
    (P : FiniteProbability Ω) (J : ι → Ω → Bool) : SignedLaw ℝ :=
  ∑ I ∈ retainedSets G D, scalar (finiteJointMoment P J I) * forwardDifference ^ I.card

def finiteBoundaryKernel (G : Finset ι) (P : FiniteProbability Ω)
    (J : ι → Ω → Bool) (I : Finset ι) : SignedLaw ℝ :=
  countLaw (orderedSuffix G I)
    (fun ω => P.weight ω * ∏ x ∈ I, indicatorValue (J x ω)) J

omit [Fintype Ω] [LinearOrder ι] in
theorem indicator_product_nonneg (J : ι → Ω → Bool) (I : Finset ι) (ω : Ω) :
    0 ≤ (∏ x ∈ I, (indicatorValue (J x ω) : ℝ)) := by
  apply Finset.prod_nonneg
  intro x _
  cases J x ω <;> simp [indicatorValue]

omit [Fintype Ω] [LinearOrder ι] in
theorem indicator_product_eq_indicator (J : ι → Ω → Bool) (I : Finset ι) (ω : Ω) :
    (∏ x ∈ I, (indicatorValue (J x ω) : ℝ)) =
      if ∀ x ∈ I, J x ω = true then 1 else 0 := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert x I hx ih =>
    rw [Finset.prod_insert hx, ih]
    by_cases hj : J x ω = true <;> simp [indicatorValue, hj]

omit [LinearOrder ι] in
theorem finiteJointMoment_nonneg (P : FiniteProbability Ω) (J : ι → Ω → Bool) (I : Finset ι) :
    0 ≤ finiteJointMoment P J I := by
  unfold finiteJointMoment finiteExpectation
  exact Finset.sum_nonneg fun ω _ => mul_nonneg (P.weight_nonneg ω) (indicator_product_nonneg J I ω)

omit [LinearOrder ι] in
@[simp]
theorem finiteJointMoment_empty (P : FiniteProbability Ω) (J : ι → Ω → Bool) :
    finiteJointMoment P J ∅ = 1 := by
  simp [finiteJointMoment, finiteExpectation, P.total_weight]

omit [LinearOrder ι] in
/-- The retained reference has mass one; its coefficients need not be positive. -/
theorem retainedCountReference_mass (G : Finset ι) (D : Finset ι → Prop)
    (P : FiniteProbability Ω) (J : ι → Ω → Bool) (h_empty : D ∅) :
    totalMass (retainedCountReference G D P J) = 1 := by
  classical
  unfold retainedCountReference
  rw [map_sum]
  have hempty : (∅ : Finset ι) ∈ retainedSets G D := by simp [retainedSets, h_empty]
  calc
    _ = totalMass (scalar (finiteJointMoment P J ∅) * forwardDifference ^ (∅ : Finset ι).card) := by
      apply Finset.sum_eq_single ∅
      · intro I _ hne
        have hc : I.card ≠ 0 := fun hz => hne (Finset.card_eq_zero.mp hz)
        simp [map_mul, map_pow, hc]
      · intro hnot
        exact False.elim (hnot hempty)
    _ = 1 := by simp

theorem finiteBoundaryKernel_nonneg (G : Finset ι) (P : FiniteProbability Ω)
    (J : ι → Ω → Bool) (I : Finset ι) (k : ℕ) : 0 ≤ (finiteBoundaryKernel G P J I).coeff k := by
  apply countLaw_coeff_nonneg
  intro ω
  exact mul_nonneg (P.weight_nonneg ω) (indicator_product_nonneg J I ω)

theorem finiteBoundaryKernel_mass (G : Finset ι) (P : FiniteProbability Ω)
    (J : ι → Ω → Bool) (I : Finset ι) :
    totalMass (finiteBoundaryKernel G P J I) = finiteJointMoment P J I := by
  exact totalMass_countLaw _ _ _

theorem finiteBoundaryKernel_l1Norm (G : Finset ι) (P : FiniteProbability Ω)
    (J : ι → Ω → Bool) (I : Finset ι) :
    l1Norm (finiteBoundaryKernel G P J I) = finiteJointMoment P J I :=
  (l1Norm_eq_totalMass_of_nonneg _ (finiteBoundaryKernel_nonneg G P J I)).trans
    (finiteBoundaryKernel_mass G P J I)

omit [Fintype Ω] in
theorem pointwise_stopped_count_identity (G : Finset ι) (D : Finset ι → Prop)
    (J : ι → Ω → Bool) (ω : Ω) (hD : Hereditary D) (h_empty : D ∅) :
    (atom (indicatorCount G J ω) : SignedLaw ℝ) =
      (∑ I ∈ retainedSets G D, scalar (∏ x ∈ I, (indicatorValue (J x ω) : ℝ)) *
        forwardDifference ^ I.card) +
      ∑ I ∈ boundarySets G D, forwardDifference ^ I.card *
        (scalar (∏ x ∈ I, (indicatorValue (J x ω) : ℝ)) *
          atom (indicatorCount (orderedSuffix G I) J ω)) := by
  have h := stopped_expansion G D (fun x => scalar (indicatorValue (J x ω) : ℝ))
    forwardDifference hD h_empty
  rw [count_atom_product] at h
  convert h using 1
  congr 1
  · apply Finset.sum_congr rfl
    intro I _
    rw [← map_prod]
    ring1
  · apply Finset.sum_congr rfl
    intro I _
    rw [← map_prod, count_atom_product]
    ring1

theorem stopped_finite_count_identity (G : Finset ι) (D : Finset ι → Prop)
    (P : FiniteProbability Ω) (J : ι → Ω → Bool) (hD : Hereditary D) (h_empty : D ∅) :
    countLaw G P.weight J = retainedCountReference G D P J +
      ∑ I ∈ boundarySets G D, forwardDifference ^ I.card * finiteBoundaryKernel G P J I := by
  unfold countLaw
  simp_rw [pointwise_stopped_count_identity G D J _ hD h_empty, mul_add,
    Finset.mul_sum, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_comm]
    unfold retainedCountReference
    apply Finset.sum_congr rfl
    intro I _
    unfold finiteJointMoment finiteExpectation
    rw [map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ω _
    rw [map_mul]
    ring1
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro I _
    unfold finiteBoundaryKernel countLaw
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω _
    rw [map_mul]
    ring1

theorem stopped_finite_count_difference (G : Finset ι) (D : Finset ι → Prop)
    (P : FiniteProbability Ω) (J : ι → Ω → Bool) (hD : Hereditary D) (h_empty : D ∅) :
    countLaw G P.weight J - retainedCountReference G D P J =
      ∑ I ∈ boundarySets G D, forwardDifference ^ I.card * finiteBoundaryKernel G P J I := by
  rw [stopped_finite_count_identity G D P J hD h_empty]
  ring1

theorem stopped_finite_count_l1_bound (G : Finset ι) (D : Finset ι → Prop)
    (P : FiniteProbability Ω) (J : ι → Ω → Bool) (hD : Hereditary D) (h_empty : D ∅) :
    l1Norm (countLaw G P.weight J - retainedCountReference G D P J) ≤
      ∑ I ∈ boundarySets G D, (2 : ℝ) ^ I.card * finiteJointMoment P J I := by
  rw [stopped_finite_count_difference G D P J hD h_empty]
  apply (l1Norm_sum _ _).trans
  apply Finset.sum_le_sum
  intro I _
  have h := l1Norm_mul (forwardDifference ^ I.card) (finiteBoundaryKernel G P J I)
  rw [finiteBoundaryKernel_l1Norm] at h
  exact h.trans (mul_le_mul_of_nonneg_right (l1Norm_forwardDifference_pow_le I.card)
    (finiteJointMoment_nonneg P J I))

end PaperP1.Probability
