module

public import PaperP1.Probability.PoissonProduct
public import Mathlib.MeasureTheory.Measure.Prod

/-! # The actual single/double Poisson reference and its stationary recurrence -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HermiteRecurrence

open MeasureTheory PaperP1.AtomicProbability PaperP1.AtomicTests PaperP1.PoissonProduct
  PaperP1.RawRecurrence

def value (z : ℕ × ℕ) : ℕ := z.1 + 2 * z.2

def law (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : ProbabilityMeasure ℕ :=
  PushforwardMass.law value (joint a b) (joint_nonneg ha hb) (joint_hasSum ha hb)

def poissonLaw (a : ℝ) (ha : 0 ≤ a) : ProbabilityMeasure ℕ :=
  ofMass (PoissonSequence.mass a) (PoissonPartialSums.mass_nonneg ha) (PoissonSequence.hasSum_mass a ha)

theorem poissonLaw_eq_mathlib (a : ℝ) (ha : 0 ≤ a) :
    (poissonLaw a ha : Measure ℕ) = ProbabilityTheory.poissonMeasure ⟨a, ha⟩ := rfl

def productLaw (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : ProbabilityMeasure (ℕ × ℕ) :=
  ⟨(poissonLaw a ha : Measure ℕ).prod (poissonLaw b hb : Measure ℕ), inferInstance⟩

theorem realMass_productLaw (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (z : ℕ × ℕ) :
    (productLaw a b ha hb : Measure (ℕ × ℕ)).real {z} = joint a b z := by
  change ((poissonLaw a ha : Measure ℕ).prod (poissonLaw b hb : Measure ℕ)).real {z} = _
  rw [show ({z} : Set (ℕ × ℕ)) = ({z.1} : Set ℕ) ×ˢ {z.2} by ext p; simp]
  rw [measureReal_prod_prod]
  change realMass (poissonLaw a ha) z.1 * realMass (poissonLaw b hb) z.2 = _
  rw [show realMass (poissonLaw a ha) z.1 = PoissonSequence.mass a z.1 from ofMass_real_singleton _ _ _ _,
    show realMass (poissonLaw b hb) z.2 = PoissonSequence.mass b z.2 from ofMass_real_singleton _ _ _ _]
  rfl

theorem law_eq_product_sum (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    law a b ha hb = (productLaw a b ha hb).map value := by
  apply Subtype.ext
  change (law a b ha hb : Measure ℕ) = ((productLaw a b ha hb).map value : Measure ℕ)
  apply Measure.ext_of_measureReal_singleton
  intro k
  change realMass (law a b ha hb) k = realMass ((productLaw a b ha hb).map value) k
  rw [law, PushforwardMass.realMass_law, PushforwardMass.realMass_map _ _ (measurable_of_countable _)]
  congr 1
  exact (funext (realMass_productLaw a b ha hb)).symm

theorem realMass_law (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (k : ℕ) :
    realMass (law a b ha hb) k =
      ∑' z : {z : ℕ × ℕ // z.1 + 2 * z.2 = k}, PoissonSequence.mass a z.val.1 * PoissonSequence.mass b z.val.2 :=
  PushforwardMass.realMass_law _ _ _ _ _

theorem value_left (z : ℕ × ℕ) : value (z.1 + 1, z.2) = value z + 1 := by unfold value; omega

theorem value_right (z : ℕ × ℕ) : value (z.1, z.2 + 1) = value z + 2 := by unfold value; omega

theorem moment_summable {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Summable (fun z : ℕ × ℕ ↦ (value z : ℝ) * joint a b z) := by
  convert (left_moment_summable ha hb).add ((right_moment_summable ha hb).mul_left 2) using 1
  funext z
  simp only [value, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring

theorem finiteFirstMoment {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : FiniteFirstMoment (law a b ha hb) := by
  have hs : Summable (fun z : ℕ × ℕ ↦ joint a b z * (value z : ℝ)) := by
    simpa only [mul_comm] using moment_summable ha hb
  have hmap := PushforwardMass.summable_test_map value (joint a b) (fun k : ℕ ↦ (k : ℝ)) hs
  change Summable (fun k : ℕ ↦ (k : ℝ) * realMass (law a b ha hb) k)
  simpa only [law, PushforwardMass.realMass_law, mul_comm] using hmap

theorem firstMoment_law {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : firstMoment (law a b ha hb) = a + 2 * b := by
  have hleft := left_test_identity ha hb (fun _ ↦ 1) (fun _ ↦ by norm_num)
  have hright := right_test_identity ha hb (fun _ ↦ 1) (fun _ ↦ by norm_num)
  simp only [mul_one, (joint_hasSum ha hb).tsum_eq] at hleft hright
  have hs : Summable (fun z : ℕ × ℕ ↦ joint a b z * (value z : ℝ)) := by
    simpa only [mul_comm] using moment_summable ha hb
  have hid := PushforwardMass.test_map value (joint a b) (fun k : ℕ ↦ (k : ℝ)) hs
  have hfun : (fun z : ℕ × ℕ ↦ joint a b z * (value z : ℝ)) = fun z ↦
      (z.1 : ℝ) * joint a b z + 2 * ((z.2 : ℝ) * joint a b z) := by
    funext z
    simp only [value, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    ring
  unfold firstMoment
  simp only [law, PushforwardMass.realMass_law]
  calc
    _ = ∑' k : ℕ, PushforwardMass.map value (joint a b) k * (k : ℝ) := tsum_congr (fun k ↦ mul_comm _ _)
    _ = _ := hid
    _ = _ := by
      rw [hfun, (left_moment_summable ha hb).tsum_add ((right_moment_summable ha hb).mul_left 2),
        tsum_mul_left, hleft, hright]

theorem operator_joint_summable {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (f : ℕ → ℝ) (hf : ∀ k, |f k| ≤ 1) :
    Summable (fun z : ℕ × ℕ ↦ joint a b z * operator (a + 2 * b) (2 * b) f (value z)) := by
  have h1 := summable_mul_unit (joint_summable ha hb) (fun z ↦ hf (value z + 1))
  have h2 := summable_mul_unit (joint_summable ha hb) (fun z ↦ hf (value z + 2))
  have h3 := summable_mul_unit (moment_summable ha hb) (fun z ↦ hf (value z))
  convert ((h1.mul_left a).add (h2.mul_left (2 * b))).sub h3 using 1
  funext z
  unfold operator
  ring

theorem stationary {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (f : ℕ → ℝ) (hf : ∀ k, |f k| ≤ 1) :
    expectation (law a b ha hb) (operator (a + 2 * b) (2 * b) f) = 0 := by
  have h1 := summable_mul_unit (joint_summable ha hb) (fun z ↦ hf (value z + 1))
  have h2 := summable_mul_unit (joint_summable ha hb) (fun z ↦ hf (value z + 2))
  have h3 := summable_mul_unit (left_moment_summable ha hb) (fun z ↦ hf (value z))
  have h4 := summable_mul_unit (right_moment_summable ha hb) (fun z ↦ hf (value z))
  have hl := left_test_identity ha hb (fun z ↦ f (value z)) (fun z ↦ hf (value z))
  have hr := right_test_identity ha hb (fun z ↦ f (value z)) (fun z ↦ hf (value z))
  simp only [value_left] at hl
  simp only [value_right] at hr
  rw [law, PushforwardMass.expectation_law _ _ _ _ _ (operator_joint_summable ha hb f hf)]
  have hfun : (fun z : ℕ × ℕ ↦ joint a b z * operator (a + 2 * b) (2 * b) f (value z)) =
      fun z ↦ a * (joint a b z * f (value z + 1)) + 2 * b * (joint a b z * f (value z + 2)) -
        ((z.1 : ℝ) * joint a b z * f (value z) + 2 * ((z.2 : ℝ) * joint a b z * f (value z))) := by
    funext z
    simp only [operator, value, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    ring
  rw [hfun, ((h1.mul_left a).add (h2.mul_left (2 * b))).tsum_sub (h3.add (h4.mul_left 2)),
    (h1.mul_left a).tsum_add (h2.mul_left (2 * b)), h3.tsum_add (h4.mul_left 2),
    tsum_mul_left, tsum_mul_left, tsum_mul_left, hl, hr]
  ring

def reference (μ θ : ℝ) (hθ : 0 ≤ θ) (hμθ : θ ≤ μ) : ProbabilityMeasure ℕ :=
  law (μ - θ) (θ / 2) (sub_nonneg.mpr hμθ) (div_nonneg hθ (by norm_num))

theorem reference_stationary (μ θ : ℝ) (hθ : 0 ≤ θ) (hμθ : θ ≤ μ)
    (f : ℕ → ℝ) (hf : ∀ k, |f k| ≤ 1) :
    expectation (reference μ θ hθ hμθ) (operator μ θ f) = 0 := by
  have h := stationary (sub_nonneg.mpr hμθ) (div_nonneg hθ (by norm_num : (0 : ℝ) ≤ 2)) f hf
  have hparam' : 2 * (θ / 2) = θ := by ring
  simpa only [reference, hparam', sub_add_cancel] using h

theorem scalar_recurrence_criterion (P : ProbabilityMeasure ℕ) (hP : FiniteFirstMoment P)
    {μ θ : ℝ} (hθ : 0 ≤ θ) (hμθ : θ < μ) (hθhalf : θ < 1 / 2) :
    totalVariation P (reference μ θ hθ hμθ.le) ≤ norm P μ θ / (1 - 2 * θ) :=
  comparison_of_stationary P _ hP (by linarith) hθ hθhalf (reference_stationary μ θ hθ hμθ.le)

/-- The closed pure-double-jump boundary theta=mu is also permitted. -/
theorem scalar_recurrence_criterion_closed (P : ProbabilityMeasure ℕ) (hP : FiniteFirstMoment P)
    {μ θ : ℝ} (hμ : 0 < μ) (hθ : 0 ≤ θ) (hμθ : θ ≤ μ) (hθhalf : θ < 1 / 2) :
    totalVariation P (reference μ θ hθ hμθ) ≤ norm P μ θ / (1 - 2 * θ) :=
  comparison_of_stationary P _ hP hμ hθ hθhalf (reference_stationary μ θ hθ hμθ)

end PaperP1.HermiteRecurrence
