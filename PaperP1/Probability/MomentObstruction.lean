module

public import PaperP1.Probability.MomentObstructionMoments

/-! # Companion T23.1: a positive perturbation invisible at every other order

The original parameter range is a corollary of the larger interval [0,2].
The total variation constant is exact. All expectations below are actual
Bochner integrals with integrability proved before the comparison.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MomentObstruction

open MeasureTheory PaperP1.Probability PaperP1.MomentObstructionMass
  PaperP1.MomentObstructionMoments PaperP1.DifferenceCoefficients PaperP1.FiniteLawEmbedding
  PaperP1.AtomicProbability Finset

theorem totalVariation_basic (m : ℕ) (hm : 1 ≤ m) (a : ℝ) (ha0 : 0 ≤ a) (ha2 : a ≤ 2) :
    totalVariation (pLaw m hm a ha0 ha2) (qLaw a ha0 ha2) = epsilon m a * (2 : ℝ) ^ m / 2 := by
  unfold totalVariation
  simp_rw [pLaw_real_singleton, qLaw_real_singleton]
  have hid (k : ℕ) : pMass m a k - qMass a k =
      epsilon m a * ((forwardDifference : SignedLaw ℝ) ^ m).coeff k := by unfold pMass; ring
  simp_rw [hid, abs_mul, abs_of_nonneg (epsilon_nonneg m a ha2)]
  rw [tsum_mul_left, ← l1Norm_eq_tsum, l1Norm_forwardDifference_pow]

theorem totalVariation_exact (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m) (a : ℝ)
    (ha0 : 0 ≤ a) (ha2 : a ≤ 2) :
    totalVariation (pLaw m hm a ha0 ha2) (qLaw a ha0 ha2) =
      (1 - a / 2) * (2 : ℝ) ^ (m - 2) / (Real.exp 1 * (m.factorial : ℝ)) := by
  rw [totalVariation_basic]
  have hpow : (2 : ℝ) ^ m = 4 * (2 : ℝ) ^ (m - 2) := by
    calc
      _ = (2 : ℝ) ^ ((m - 2) + 2) :=
        congrArg (fun n : ℕ ↦ (2 : ℝ) ^ n) (Nat.sub_add_cancel hm2).symm
      _ = _ := by rw [pow_add]; norm_num; ring
  unfold epsilon sourceConstant
  rw [hpow, Real.exp_neg]
  field_simp
  ring

theorem exponential_integrable (m : ℕ) (hm : 1 ≤ m) (a : ℝ) (ha0 : 0 ≤ a)
    (ha2 : a ≤ 2) (t : ℝ) :
    Integrable (fun k : ℕ ↦ Real.exp (t * k)) (pLaw m hm a ha0 ha2 : Measure ℕ) := by
  apply (ofMass_integrable_iff _ _ _ _).mpr
  have h := (hasSum_pMass_weighted m a (fun k : ℕ ↦ Real.exp (t * k)) (hasSum_qMass_exp a t)).summable
  simpa only [abs_of_pos (Real.exp_pos _)] using h

theorem exponential_moment_le (m : ℕ) (hm : 1 ≤ m) (a : ℝ) (ha0 : 0 ≤ a)
    (ha2 : a ≤ 2) (t A : ℝ) (hA : a ≤ A) :
    (∫ k : ℕ, Real.exp (t * k) ∂(pLaw m hm a ha0 ha2 : Measure ℕ)) ≤
      3 / 2 * Real.exp (Real.exp t - 1) * (1 + A / 2 * (Real.exp t - 1) ^ 2) := by
  have hq := hasSum_qMass_exp a t
  have hp := hasSum_pMass_weighted m a (fun k : ℕ ↦ Real.exp (t * k)) hq
  have hbound (k : ℕ) : pMass m a k * Real.exp (t * k) ≤
      (3 / 2) * (qMass a k * Real.exp (t * k)) := by
    have h := mul_le_mul_of_nonneg_right (pMass_pointwise_bounds m a ha0 ha2 k).2
      (Real.exp_pos (t * k)).le
    simpa only [mul_assoc] using h
  have hsum := hasSum_le hbound hp.summable.hasSum (hq.mul_left (3 / 2))
  change (∫ k : ℕ, Real.exp (t * k) ∂(ofMass _ _ _ : Measure ℕ)) ≤ _
  rw [ofMass_integral]
  have hpoly : 1 + a / 2 * (Real.exp t - 1) ^ 2 ≤ 1 + A / 2 * (Real.exp t - 1) ^ 2 := by
    nlinarith [sq_nonneg (Real.exp t - 1)]
  calc
    _ ≤ (3 / 2) * (Real.exp (Real.exp t - 1) * (1 + a / 2 * (Real.exp t - 1) ^ 2)) := hsum
    _ ≤ (3 / 2) * (Real.exp (Real.exp t - 1) * (1 + A / 2 * (Real.exp t - 1) ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpoly (Real.exp_pos _).le) (by norm_num)
    _ = _ := by ring

theorem pointwise_law_bounds (m : ℕ) (hm : 1 ≤ m) (a : ℝ) (ha0 : 0 ≤ a)
    (ha2 : a ≤ 2) (k : ℕ) :
    (qLaw a ha0 ha2 : Measure ℕ).real {k} / 2 ≤ (pLaw m hm a ha0 ha2 : Measure ℕ).real {k} ∧
      (pLaw m hm a ha0 ha2 : Measure ℕ).real {k} ≤ 3 / 2 * (qLaw a ha0 ha2 : Measure ℕ).real {k} := by
  rw [pLaw_real_singleton, qLaw_real_singleton]
  exact pMass_pointwise_bounds m a ha0 ha2 k

/-- The entire proposition on [0,2], including all real exponential parameters.
At a=2 the perturbation vanishes. The source's range [0,1] is below. -/
theorem companion_T23_1_extended (m : ℕ) (hm : 3 ≤ m) (a : ℝ) (ha0 : 0 ≤ a) (ha2 : a ≤ 2) :
    (∀ k : ℕ, (qLaw a ha0 ha2 : Measure ℕ).real {k} / 2 ≤
        (pLaw m (by omega) a ha0 ha2 : Measure ℕ).real {k} ∧
      (pLaw m (by omega) a ha0 ha2 : Measure ℕ).real {k} ≤
        3 / 2 * (qLaw a ha0 ha2 : Measure ℕ).real {k}) ∧
      (∀ j : ℕ, j ≠ m →
        (∫ k, (k.descFactorial j : ℝ) ∂(pLaw m (by omega) a ha0 ha2 : Measure ℕ)) =
          ∫ k, (k.descFactorial j : ℝ) ∂(qLaw a ha0 ha2 : Measure ℕ)) ∧
      totalVariation (pLaw m (by omega) a ha0 ha2) (qLaw a ha0 ha2) =
        (1 - a / 2) * (2 : ℝ) ^ (m - 2) / (Real.exp 1 * (m.factorial : ℝ)) ∧
      (∀ t : ℝ, Integrable (fun k : ℕ ↦ Real.exp (t * k))
          (pLaw m (by omega) a ha0 ha2 : Measure ℕ) ∧
        (∫ k : ℕ, Real.exp (t * k) ∂(pLaw m (by omega) a ha0 ha2 : Measure ℕ)) ≤
          3 / 2 * Real.exp (Real.exp t - 1) * (1 + (Real.exp t - 1) ^ 2)) := by
  refine ⟨pointwise_law_bounds m (by omega) a ha0 ha2,
    factorial_moment_eq_of_ne m (by omega) a ha0 ha2,
    totalVariation_exact m (by omega) (by omega) a ha0 ha2, ?_⟩
  intro t
  refine ⟨exponential_integrable m (by omega) a ha0 ha2 t, ?_⟩
  simpa only [div_self (by norm_num : (2 : ℝ) ≠ 0), one_mul] using
    exponential_moment_le m (by omega) a ha0 ha2 t 2 ha2

/-- Original parameter range, with the original explicit uniform exponential bound. -/
theorem companion_T23_1_exponential (m : ℕ) (hm : 3 ≤ m) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (t : ℝ) :
    Integrable (fun k : ℕ ↦ Real.exp (t * k))
        (pLaw m (by omega) a ha0 (by linarith) : Measure ℕ) ∧
      (∫ k : ℕ, Real.exp (t * k) ∂(pLaw m (by omega) a ha0 (by linarith) : Measure ℕ)) ≤
        3 / 2 * Real.exp (Real.exp t - 1) * (1 + (1 / 2) * (Real.exp t - 1) ^ 2) :=
  ⟨exponential_integrable m (by omega) a ha0 (by linarith) t,
    exponential_moment_le m (by omega) a ha0 (by linarith) t 1 ha1⟩

/-- Every conclusion in the original interval; the unique changed factorial
order is proved explicitly, with integrability of both laws. -/
theorem companion_T23_1 (m : ℕ) (hm : 3 ≤ m) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (∀ k : ℕ, (qLaw a ha0 (by linarith) : Measure ℕ).real {k} / 2 ≤
        (pLaw m (by omega) a ha0 (by linarith) : Measure ℕ).real {k} ∧
      (pLaw m (by omega) a ha0 (by linarith) : Measure ℕ).real {k} ≤
        3 / 2 * (qLaw a ha0 (by linarith) : Measure ℕ).real {k}) ∧
      (∀ j : ℕ, Integrable (fun k : ℕ ↦ (k.descFactorial j : ℝ))
          (pLaw m (by omega) a ha0 (by linarith) : Measure ℕ) ∧
        Integrable (fun k : ℕ ↦ (k.descFactorial j : ℝ)) (qLaw a ha0 (by linarith) : Measure ℕ) ∧
        (((∫ k, (k.descFactorial j : ℝ) ∂(pLaw m (by omega) a ha0 (by linarith) : Measure ℕ)) =
          ∫ k, (k.descFactorial j : ℝ) ∂(qLaw a ha0 (by linarith) : Measure ℕ)) ↔ j ≠ m)) ∧
      totalVariation (pLaw m (by omega) a ha0 (by linarith)) (qLaw a ha0 (by linarith)) =
        (1 - a / 2) * (2 : ℝ) ^ (m - 2) / (Real.exp 1 * (m.factorial : ℝ)) ∧
      (∀ t : ℝ, Integrable (fun k : ℕ ↦ Real.exp (t * k))
          (pLaw m (by omega) a ha0 (by linarith) : Measure ℕ) ∧
        (∫ k : ℕ, Real.exp (t * k) ∂(pLaw m (by omega) a ha0 (by linarith) : Measure ℕ)) ≤
          3 / 2 * Real.exp (Real.exp t - 1) * (1 + (1 / 2) * (Real.exp t - 1) ^ 2)) := by
  refine ⟨pointwise_law_bounds m (by omega) a ha0 (by linarith), ?_,
    totalVariation_exact m (by omega) (by omega) a ha0 (by linarith),
    companion_T23_1_exponential m hm a ha0 ha1⟩
  intro j
  refine ⟨pLaw_factorial_integrable m (by omega) a ha0 (by linarith) j,
    qLaw_factorial_integrable a ha0 (by linarith) j, ?_⟩
  exact factorial_moment_eq_iff m (by omega) a ha0 (by linarith) (by linarith) j

end PaperP1.MomentObstruction
