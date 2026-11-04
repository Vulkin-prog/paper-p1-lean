module

public import PaperP1.Probability.FirstWasserstein
public import PaperP1.Model.FiniteDeletedIntensity

/-! # Exact finite couplings of one-edge deletion and simultaneous isolation

The cost is the positive second factorial moment of the original active-edge
count. The same original sample produces both observations; no independent
replacement field or target asymptotic estimate enters the comparison.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteOnceAllCoupling

open Finset PaperP1.Algebra PaperP1.Probability PaperP1.PositionalFiniteLaw
  PaperP1.PositionalPairDeletion PaperP1.PositionalCountProjection

variable {ι Ω : Type*}

theorem cast_factorial_two (k : ℕ) :
    ((k * (k - 1) : ℕ) : ℝ) = (k : ℝ) * ((k : ℝ) - 1) := by
  cases k with
  | zero => norm_num
  | succ k => simp only [Nat.add_sub_cancel, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one]; ring

theorem absolute_count_cost (E : Finset (Finset ι)) (v : Configuration ι)
    (hv : ∀ x, v x ≤ 1) (hE : ∀ e ∈ E, e.card = 2) :
    |(oneCount E v : ℝ) - (totalCount (isolate E v) : ℝ)| ≤
      ((activeEdges E v).card : ℝ) * (((activeEdges E v).card : ℝ) - 1) := by
  have hc := one_all_count_cost E v hv hE
  have hord : (totalCount (isolate E v) : ℝ) ≤ (oneCount E v : ℝ) := by exact_mod_cast hc.1
  have hh : ((oneCount E v - totalCount (isolate E v) : ℕ) : ℝ) ≤
      (((activeEdges E v).card * ((activeEdges E v).card - 1) : ℕ) : ℝ) := by exact_mod_cast hc.2
  rwa [Nat.cast_sub hc.1, cast_factorial_two, ← abs_of_nonneg (sub_nonneg.mpr hord)] at hh

theorem disagreement_cost (E : Finset (Finset ι)) (v : Configuration ι)
    (hv : ∀ x, v x ≤ 1) (hE : ∀ e ∈ E, e.card = 2) :
    (if oneCount E v ≠ totalCount (isolate E v) then (1 : ℝ) else 0) ≤
      (((activeEdges E v).card : ℝ) * (((activeEdges E v).card : ℝ) - 1)) / 2 := by
  classical
  have hc := one_all_count_cost E v hv hE
  by_cases heq : oneCount E v = totalCount (isolate E v)
  · simp only [heq, ne_eq, not_true_eq_false, ite_false]
    rw [← cast_factorial_two]
    positivity
  · have hk : 2 ≤ (activeEdges E v).card := by
      by_contra h
      have hk1 : (activeEdges E v).card ≤ 1 := by omega
      have hz : (activeEdges E v).card - 1 = 0 := by omega
      rw [hz, mul_zero] at hc
      omega
    have htwo : 2 ≤ (activeEdges E v).card * ((activeEdges E v).card - 1) := by
      calc
        2 = 2 * 1 := by decide
        _ ≤ _ := Nat.mul_le_mul hk (by omega)
    have hr : (2 : ℝ) ≤ (((activeEdges E v).card * ((activeEdges E v).card - 1) : ℕ) : ℝ) :=
      by exact_mod_cast htwo
    rw [cast_factorial_two] at hr
    simp only [heq, ne_eq, not_false_eq_true, ite_true]
    linarith only [hr]

variable [Fintype Ω]

def onceObservation (G : Finset ι) (J : ι → Ω → Bool) (E : Finset (Finset ι)) (ω : Ω) : ℕ :=
  oneCount E (configuration G J ω)

def allObservation (G : Finset ι) (J : ι → Ω → Bool) (E : Finset (Finset ι)) (ω : Ω) : ℕ :=
  totalCount (isolate E (configuration G J ω))

def factorialCost (P : FiniteProbability Ω) (G : Finset ι) (J : ι → Ω → Bool)
    (E : Finset (Finset ι)) : ℝ :=
  finiteExpectation P.weight (fun ω ↦ ((activeEdges E (configuration G J ω)).card : ℝ) *
    (((activeEdges E (configuration G J ω)).card : ℝ) - 1))

theorem totalVariation_bound (P : FiniteProbability Ω) (G : Finset ι) (J : ι → Ω → Bool)
    (E : Finset (Finset ι)) (hE : ∀ e ∈ E, e.card = 2) :
    AtomicProbability.totalVariation
      (FiniteObservationLaw.law P (onceObservation G J E))
      (FiniteObservationLaw.law P (allObservation G J E)) ≤ factorialCost P G J E / 2 := by
  apply (FiniteObservationLaw.coupling _ _ _).trans
  calc
    _ ≤ finiteExpectation P.weight (fun ω ↦
        (((activeEdges E (configuration G J ω)).card : ℝ) *
          (((activeEdges E (configuration G J ω)).card : ℝ) - 1)) / 2) :=
      finiteExpectation_mono P (fun ω ↦ disagreement_cost E (configuration G J ω)
        (PositionalDeletedFields.configuration_binary G J ω) hE)
    _ = _ := by simp only [div_eq_mul_inv, finiteExpectation_mul_const, factorialCost]

theorem wasserstein_bound (P : FiniteProbability Ω) (G : Finset ι) (J : ι → Ω → Bool)
    (E : Finset (Finset ι)) (hE : ∀ e ∈ E, e.card = 2) :
    FirstWasserstein.distance
      (FiniteObservationLaw.law P (onceObservation G J E))
      (FiniteObservationLaw.law P (allObservation G J E))
      ⟨FirstWasserstein.finitePlan P (onceObservation G J E) (allObservation G J E)⟩ ≤
        factorialCost P G J E := by
  exact (FirstWasserstein.finite_coupling_bound _ _ _).trans
    (finiteExpectation_mono P (fun ω ↦ absolute_count_cost E (configuration G J ω)
      (PositionalDeletedFields.configuration_binary G J ω) hE))

end PaperP1.FiniteOnceAllCoupling
