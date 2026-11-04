module

public import PaperP1.Probability.FiniteObservationLaw

/-! # First Wasserstein transport on the naturals and the actual finite coupling

Transport plans have the prescribed probability marginals and absolutely
summable cost. The real-valued infimum is used on the domain where such a
finite-cost plan exists. Every finite observation pair has such a plan.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FirstWasserstein

open Finset MeasureTheory PaperP1.Algebra PaperP1.Probability PaperP1.AtomicProbability

structure Plan (P Q : ProbabilityMeasure ℕ) where
  mass : ℕ × ℕ → ℝ
  nonneg : ∀ p, 0 ≤ mass p
  row : ∀ i, HasSum (fun j ↦ mass (i, j)) (realMass P i)
  column : ∀ j, HasSum (fun i ↦ mass (i, j)) (realMass Q j)
  cost_summable : Summable (fun p ↦ mass p * |(p.1 : ℝ) - (p.2 : ℝ)|)

def cost {P Q : ProbabilityMeasure ℕ} (π : Plan P Q) : ℝ :=
  ∑' p, π.mass p * |(p.1 : ℝ) - (p.2 : ℝ)|

theorem cost_nonneg {P Q : ProbabilityMeasure ℕ} (π : Plan P Q) : 0 ≤ cost π :=
  tsum_nonneg (fun p ↦ mul_nonneg (π.nonneg p) (abs_nonneg _))

theorem mass_summable {P Q : ProbabilityMeasure ℕ} (π : Plan P Q) : Summable π.mass := by
  have he (i : ℕ) : (∑' j, π.mass (i, j)) = realMass P i := (π.row i).tsum_eq
  have houter : Summable (fun i ↦ ∑' j, π.mass (i, j)) := by
    simpa only [he] using (hasSum_realMass P).summable
  exact (summable_prod_of_nonneg π.nonneg).mpr ⟨fun i ↦ (π.row i).summable, houter⟩

theorem total_mass {P Q : ProbabilityMeasure ℕ} (π : Plan P Q) : (∑' p, π.mass p) = 1 := by
  rw [(mass_summable π).tsum_prod]
  have he (i : ℕ) : (∑' j, π.mass (i, j)) = realMass P i := (π.row i).tsum_eq
  simpa only [he] using (hasSum_realMass P).tsum_eq

def distance (P Q : ProbabilityMeasure ℕ) (_hPQ : Nonempty (Plan P Q)) : ℝ :=
  sInf (Set.range (fun π : Plan P Q ↦ cost π))

theorem costs_bddBelow (P Q : ProbabilityMeasure ℕ) :
    BddBelow (Set.range (fun π : Plan P Q ↦ cost π)) := by
  refine ⟨0, ?_⟩
  rintro r ⟨π, rfl⟩
  exact cost_nonneg π

theorem distance_le_cost (P Q : ProbabilityMeasure ℕ) (hPQ : Nonempty (Plan P Q)) (π : Plan P Q) :
    distance P Q hPQ ≤ cost π := csInf_le (costs_bddBelow P Q) (Set.mem_range_self π)

theorem distance_nonneg (P Q : ProbabilityMeasure ℕ) (hPQ : Nonempty (Plan P Q)) :
    0 ≤ distance P Q hPQ := by
  obtain ⟨π⟩ := hPQ
  apply le_csInf (show (Set.range (fun π : Plan P Q ↦ cost π)).Nonempty from
    ⟨cost π, Set.mem_range_self π⟩)
  rintro r ⟨ρ, rfl⟩
  exact cost_nonneg ρ

variable {Ω : Type*} [Fintype Ω]

def finiteMass (P : FiniteProbability Ω) (Z W : Ω → ℕ) (p : ℕ × ℕ) : ℝ :=
  ∑ ω, if (Z ω, W ω) = p then P.weight ω else 0

theorem hasSum_finite_test (P : FiniteProbability Ω) (Z W : Ω → ℕ) (f : ℕ × ℕ → ℝ) :
    HasSum (fun p ↦ finiteMass P Z W p * f p)
      (finiteExpectation P.weight (fun ω ↦ f (Z ω, W ω))) := by
  classical
  have hterm (ω : Ω) : HasSum (fun p : ℕ × ℕ ↦
      (if (Z ω, W ω) = p then P.weight ω else 0) * f p) (P.weight ω * f (Z ω, W ω)) := by
    have hh := hasSum_ite_eq' (Z ω, W ω) (P.weight ω * f (Z ω, W ω))
    convert hh using 1
    funext p
    by_cases hp : (Z ω, W ω) = p
    · subst p
      simp
    · simp only [hp, ite_false, zero_mul]
  have hh := hasSum_sum (s := univ) (fun ω _hω ↦ hterm ω)
  convert hh using 1
  · funext p
    simp only [finiteMass, sum_mul]
  · rfl

def finitePlan (P : FiniteProbability Ω) (Z W : Ω → ℕ) :
    Plan (FiniteObservationLaw.law P Z) (FiniteObservationLaw.law P W) where
  mass := finiteMass P Z W
  nonneg := fun p ↦ sum_nonneg (fun ω _hω ↦ by split_ifs; exact P.weight_nonneg ω; exact le_rfl)
  row := by
    intro i
    have hterm (ω : Ω) : HasSum (fun j : ℕ ↦ if (Z ω, W ω) = (i, j) then P.weight ω else 0)
        (if Z ω = i then P.weight ω else 0) := by
      by_cases hz : Z ω = i
      · simpa only [Prod.mk.injEq, hz, true_and, ite_true] using hasSum_ite_eq' (W ω) (P.weight ω)
      · simpa only [Prod.mk.injEq, hz, false_and, ite_false] using
          (hasSum_zero : HasSum (fun _j : ℕ ↦ (0 : ℝ)) 0)
    have hh := hasSum_sum (s := univ) (fun ω _hω ↦ hterm ω)
    convert hh using 1
    · funext j
      rfl
    · rw [FiniteObservationLaw.realMass_eq]
      simp only [finiteExpectation, mul_ite, mul_one, mul_zero]
  column := by
    intro j
    have hterm (ω : Ω) : HasSum (fun i : ℕ ↦ if (Z ω, W ω) = (i, j) then P.weight ω else 0)
        (if W ω = j then P.weight ω else 0) := by
      by_cases hw : W ω = j
      · simpa only [Prod.mk.injEq, hw, and_true, ite_true] using hasSum_ite_eq' (Z ω) (P.weight ω)
      · simpa only [Prod.mk.injEq, hw, and_false, ite_false] using
          (hasSum_zero : HasSum (fun _i : ℕ ↦ (0 : ℝ)) 0)
    have hh := hasSum_sum (s := univ) (fun ω _hω ↦ hterm ω)
    convert hh using 1
    · funext i
      rfl
    · rw [FiniteObservationLaw.realMass_eq]
      simp only [finiteExpectation, mul_ite, mul_one, mul_zero]
  cost_summable := (hasSum_finite_test P Z W (fun p ↦ |(p.1 : ℝ) - (p.2 : ℝ)|)).summable

theorem finite_cost (P : FiniteProbability Ω) (Z W : Ω → ℕ) :
    cost (finitePlan P Z W) = finiteExpectation P.weight (fun ω ↦ |(Z ω : ℝ) - (W ω : ℝ)|) :=
  (hasSum_finite_test P Z W (fun p ↦ |(p.1 : ℝ) - (p.2 : ℝ)|)).tsum_eq

theorem finite_coupling_bound (P : FiniteProbability Ω) (Z W : Ω → ℕ) :
    distance (FiniteObservationLaw.law P Z) (FiniteObservationLaw.law P W) ⟨finitePlan P Z W⟩ ≤
      finiteExpectation P.weight (fun ω ↦ |(Z ω : ℝ) - (W ω : ℝ)|) := by
  exact (distance_le_cost _ _ _ (finitePlan P Z W)).trans_eq (finite_cost P Z W)

end PaperP1.FirstWasserstein
