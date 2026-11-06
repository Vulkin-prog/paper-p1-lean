module

public import PaperP1.Arithmetic.IntegralCurveGridCount
public import PaperP1.Arithmetic.CurveProjectionHeightBudget
public import PaperP1.Arithmetic.IntegerPopulationBoxBudget
public import PaperP1.Arithmetic.QuadraticPlaneUniformBound

/-! # The actual dimension-dependent quadratic-degree curve bound over every original characteristic-zero coefficient field -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UniformIntegralCurveCount

universe u

open MvPolynomial QuadraticDegreeUniformFieldCount
attribute [local instance] MvPolynomial.gradedAlgebra

def constant (n : ℕ) : ℝ :=
  (QuadraticAllDegreePlaneCount.constant.{u} + 1) * (CurveProjectionHeightBudget.profileFactor n : ℝ) +
    ((3 ^ n : ℕ) : ℝ)

theorem constant_pos (n : ℕ) : 0 < constant.{u} n := by
  have hC := QuadraticAllDegreePlaneCount.constant_pos.{u}
  unfold constant
  positivity

theorem population_bound {F : Type u} [Field F] [CharZero F] (n : ℕ)
    (I : Ideal (MvPolynomial (Fin n) F)) (hI : I.IsHomogeneous (homogeneousSubmodule (Fin n) F))
    (hprime : I.IsPrime) (d : ℕ) (hd : 0 < d) (b₀ : ℚ)
    (hp : GradedHilbertPolynomial.IsHilbertPolynomial
      (HomogeneousQuotientGrading.piece (homogeneousSubmodule (Fin n) F) I)
      (Polynomial.C (d : ℚ) * Polynomial.X + Polynomial.C b₀))
    (z : Fin n) (H : ℕ) (hH : 1 ≤ H) (S : Finset (Fin n → ℤ))
    (hnormal : ∀ w ∈ S, w z = 1)
    (hcurve : ∀ w ∈ S, ∀ P ∈ I, eval (fun i ↦ (w i : F)) P = 0)
    (hheight : ∀ w ∈ S, ∀ i, (w i).natAbs ≤ H) :
    (S.card : ℝ) ≤ constant.{u} n * profile d H := by
  have hC := QuadraticAllDegreePlaneCount.constant_pos.{u}
  have hprofile : 0 ≤ profile d H := (sq_nonneg (d : ℝ)).trans (degree_square_le_profile d H hH)
  have hplane : (QuadraticAllDegreePlaneCount.constant.{u} + 1) *
      (CurveProjectionHeightBudget.profileFactor n : ℝ) ≤ constant.{u} n :=
    le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hbox : ((3 ^ n : ℕ) : ℝ) ≤ constant.{u} n := by
    apply le_add_of_nonneg_left
    positivity
  by_cases hunit : H = 1
  · subst H
    exact (IntegerPopulationBoxBudget.unit_height_profile n d hd S hheight).trans
      (mul_le_mul_of_nonneg_right hbox hprofile)
  have hn : 1 ≤ n := by have := z.isLt; omega
  by_cases hcap : d ≤ H ^ n
  · have hc := IntegralCurveGridCount.population_bound n I hI hprime d hd b₀ hp z H hH
      S hnormal hcurve hheight
    have ht := CurveProjectionHeightBudget.profile_bound n d H hn hd (by omega) hcap
    have hb := hc.trans (mul_le_mul_of_nonneg_left ht (by linarith only [hC]))
    calc
      _ ≤ (QuadraticAllDegreePlaneCount.constant.{u} + 1) *
          ((CurveProjectionHeightBudget.profileFactor n : ℝ) * profile d H) := hb
      _ = ((QuadraticAllDegreePlaneCount.constant.{u} + 1) *
          (CurveProjectionHeightBudget.profileFactor n : ℝ)) * profile d H := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hplane hprofile
  · exact (IntegerPopulationBoxBudget.large_degree_profile n d H hd hH (by omega) S hheight).trans
      (mul_le_mul_of_nonneg_right hbox hprofile)

def realConstant (n : ℕ) : ℝ := constant.{u} n * (2 / Real.log 2) ^ 17

theorem realConstant_pos (n : ℕ) : 0 < realConstant.{u} n := by
  have hc := constant_pos.{u} n
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold realConstant
  positivity

theorem real_population_bound {F : Type u} [Field F] [CharZero F] (n : ℕ)
    (I : Ideal (MvPolynomial (Fin n) F)) (hI : I.IsHomogeneous (homogeneousSubmodule (Fin n) F))
    (hprime : I.IsPrime) (d : ℕ) (hd : 0 < d) (b₀ : ℚ)
    (hp : GradedHilbertPolynomial.IsHilbertPolynomial
      (HomogeneousQuotientGrading.piece (homogeneousSubmodule (Fin n) F) I)
      (Polynomial.C (d : ℚ) * Polynomial.X + Polynomial.C b₀))
    (z : Fin n) (H : ℝ) (hH : 2 < H) (S : Finset (Fin n → ℤ))
    (hnormal : ∀ w ∈ S, w z = 1)
    (hcurve : ∀ w ∈ S, ∀ P ∈ I, eval (fun i ↦ (w i : F)) P = 0)
    (hheight : ∀ w ∈ S, ∀ i, |(w i : ℝ)| ≤ H) :
    (S.card : ℝ) ≤ realConstant.{u} n * (d : ℝ) ^ 2 * H ^ (1 / (d : ℝ)) * Real.log H ^ 17 := by
  let N : ℕ := ⌊H⌋₊
  have hN : 1 ≤ N := by
    apply Nat.le_floor
    norm_num only [Nat.cast_one]
    linarith only [hH]
  have hNH : (N : ℝ) ≤ H := Nat.floor_le (by linarith)
  have hheightN : ∀ w ∈ S, ∀ i, (w i).natAbs ≤ N := by
    intro w hw i
    have hm := (IntegerGridTheorem.floor_box_iff H (by linarith) (w i)).mpr (hheight w hw i)
    have hh := (CurveIntegerFibres.mem_offsetBox N (w i)).mp hm
    rw [Int.abs_eq_natAbs] at hh
    exact_mod_cast hh
  have hc := population_bound n I hI hprime d hd b₀ hp z N hN S hnormal hcurve hheightN
  have hC := constant_pos.{u} n
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogH : 0 ≤ Real.log H := Real.log_nonneg (by linarith only [hH])
  have hl := QuadraticPlaneUniformBound.binary_budget_le_real_log N hN H hH hNH
  have hlog := pow_le_pow_left₀ (Nat.cast_nonneg _) hl 17
  have hroot : (N : ℝ) ^ (1 / (d : ℝ)) ≤ H ^ (1 / (d : ℝ)) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hNH (by positivity)
  calc
    _ ≤ constant.{u} n * profile d N := hc
    _ = constant.{u} n * (d : ℝ) ^ 2 *
        (DegreeUniformAffineParameters.logarithmicBudget N : ℝ) ^ 17 * (N : ℝ) ^ (1 / (d : ℝ)) := by
      unfold profile
      ring
    _ ≤ constant.{u} n * (d : ℝ) ^ 2 * ((2 / Real.log 2) * Real.log H) ^ 17 * H ^ (1 / (d : ℝ)) := by
      gcongr
    _ = _ := by rw [mul_pow]; unfold realConstant; ring

end PaperP1.UniformIntegralCurveCount
