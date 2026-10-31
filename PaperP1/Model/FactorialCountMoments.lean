module

public import PaperP1.Probability.FactorialTuples
public import PaperP1.Model.CountObservables
public import PaperP1.Model.InfiniteJointMoments

/-! # Actual factorial moments as sums over all ordered distinct tuples -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FactorialCountMoments

open MeasureTheory PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
open PaperP1.Model.InfiniteRademacher PaperP1.Probability PaperP1.Algebra
open CountObservables Finset

local instance factorialCountMeasurableF2 : MeasurableSpace F₂ := ⊤

def factorialCountMoment (G : Finset ℕ) (L r : ℕ) : ℝ :=
  ∫ ω, ((infiniteStartCount G L ω).descFactorial r : ℝ) ∂infiniteRademacherMeasure

theorem factorialCountMoment_eq_falling_product (G : Finset ℕ) (L r : ℕ) :
    factorialCountMoment G L r =
      ∫ ω, ∏ i ∈ range r, ((infiniteStartCount G L ω : ℝ) - i)
        ∂infiniteRademacherMeasure := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ω ↦
    cast_descFactorial_eq_falling_product (infiniteStartCount G L ω) r

theorem factorialCountMoment_eq_finite {N L : ℕ} {G : Finset ℕ}
    (hG : G ⊆ dyadicBlock N) (r : ℕ) :
    factorialCountMoment G L r = finiteExpectation (cylinderProbability (dyadicCutoff N L)).weight
      (fun σ ↦ ((indicatorCount G (fun x ↦ startIndicator x L) σ).descFactorial r : ℝ)) :=
  count_observable_integral_eq_finite hG (fun n ↦ (n.descFactorial r : ℝ))

theorem factorialCountMoment_nonneg {N L : ℕ} {G : Finset ℕ}
    (hG : G ⊆ dyadicBlock N) (r : ℕ) : 0 ≤ factorialCountMoment G L r := by
  rw [factorialCountMoment_eq_finite hG]
  exact finiteExpectation_nonneg _ (fun _ ↦ Nat.cast_nonneg _)

theorem factorialCountMoment_two {N L : ℕ} {G : Finset ℕ}
    (hG : G ⊆ dyadicBlock N) :
    factorialCountMoment G L 2 = countMoment G L 2 - countMoment G L 1 := by
  rw [factorialCountMoment_eq_finite hG, countMoment_eq_finite hG,
    countMoment_eq_finite hG, ← finiteExpectation_sub]
  congr 1
  funext σ
  rw [cast_descFactorial_eq_falling_product]
  simp only [prod_range_succ, prod_range_zero, Nat.cast_zero,
    Nat.cast_one, sub_zero, pow_one]
  ring

theorem sum_tuple_joint_moments {N L : ℕ} {G : Finset ℕ}
    (hG : G ⊆ dyadicBlock N) (r : ℕ) :
    (∑ t : OrderedTuple G r, infiniteJointMoment L (tupleValues t)) = factorialCountMoment G L r := by
  classical
  rw [factorialCountMoment_eq_finite hG]
  calc
    _ = ∑ t : OrderedTuple G r,
        finiteExpectation (cylinderProbability (dyadicCutoff N L)).weight
          (fun σ ↦ ∏ x ∈ tupleValues t, (indicatorValue (startIndicator x L σ) : ℝ)) := by
      apply sum_congr rfl
      intro t _
      exact infiniteJointMoment_eq_finite (dyadicCutoff N L) L (tupleValues t)
        (dyadic_subset_cutoff ((tupleValues_subset t).trans hG))
    _ = finiteExpectation (cylinderProbability (dyadicCutoff N L)).weight
        (fun σ ↦ ∑ t : OrderedTuple G r,
          ∏ x ∈ tupleValues t, (indicatorValue (startIndicator x L σ) : ℝ)) :=
      (finiteExpectation_sum _ _ _).symm
    _ = _ := by
      congr 1
      funext σ
      exact sum_tuple_products_eq_descFactorial G (fun x ↦ startIndicator x L) σ r

end PaperP1.FactorialCountMoments
