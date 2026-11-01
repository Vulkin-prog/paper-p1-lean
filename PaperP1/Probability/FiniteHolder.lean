module

public import PaperP1.Algebra.FiniteExpectation
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-! # Finite weighted Holder with an arbitrary finite number of factors -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteHolder

open scoped ENNReal
open Finset MeasureTheory PaperP1.Algebra

theorem sum_geometric_holder {Ω ι : Type*} [Fintype Ω]
    (I : Finset ι) (F : ι → Ω → ℝ) (α : ι → ℝ)
    (hF : ∀ i ∈ I, ∀ ω, 0 ≤ F i ω) (hα : ∀ i ∈ I, 0 ≤ α i) (hsum : ∑ i ∈ I, α i = 1) :
    (∑ ω, ∏ i ∈ I, (F i ω) ^ α i) ≤ ∏ i ∈ I, (∑ ω, F i ω) ^ α i := by
  classical
  let _ : MeasurableSpace Ω := ⊤
  have h := ENNReal.lintegral_prod_norm_pow_le (μ := Measure.count)
    (f := fun i ω ↦ ENNReal.ofReal (F i ω)) (p := α) I
    (fun i _ ↦ (measurable_of_finite (fun ω ↦ ENNReal.ofReal (F i ω))).aemeasurable) hsum hα
  simp only [lintegral_fintype, Measure.count_singleton, mul_one] at h
  have hlhs : ENNReal.ofReal (∑ ω, ∏ i ∈ I, (F i ω) ^ α i) =
      ∑ ω, ∏ i ∈ I, (ENNReal.ofReal (F i ω)) ^ α i := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun ω _ ↦ prod_nonneg fun i hi ↦ Real.rpow_nonneg (hF i hi ω) _)]
    apply sum_congr rfl
    intro ω _
    rw [ENNReal.ofReal_prod_of_nonneg (fun i hi ↦ Real.rpow_nonneg (hF i hi ω) _)]
    apply prod_congr rfl
    intro i hi
    exact (ENNReal.ofReal_rpow_of_nonneg (hF i hi ω) (hα i hi)).symm
  have hrhs : ENNReal.ofReal (∏ i ∈ I, (∑ ω, F i ω) ^ α i) =
      ∏ i ∈ I, (∑ ω, ENNReal.ofReal (F i ω)) ^ α i := by
    rw [ENNReal.ofReal_prod_of_nonneg (fun i hi ↦ Real.rpow_nonneg (sum_nonneg fun ω _ ↦ hF i hi ω) _)]
    apply prod_congr rfl
    intro i hi
    rw [← ENNReal.ofReal_rpow_of_nonneg (sum_nonneg fun ω _ ↦ hF i hi ω) (hα i hi),
      ENNReal.ofReal_sum_of_nonneg (fun ω _ ↦ hF i hi ω)]
  rw [← hlhs, ← hrhs] at h
  exact (ENNReal.ofReal_le_ofReal_iff (prod_nonneg fun i hi ↦
    Real.rpow_nonneg (sum_nonneg fun ω _ ↦ hF i hi ω) _)).mp h

theorem weighted_geometric_holder {Ω ι : Type*} [Fintype Ω]
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (I : Finset ι) (F : ι → Ω → ℝ) (α : ι → ℝ)
    (hF : ∀ i ∈ I, ∀ ω, 0 ≤ F i ω) (hα : ∀ i ∈ I, 0 ≤ α i) (hsum : ∑ i ∈ I, α i = 1) :
    finiteExpectation w (fun ω ↦ ∏ i ∈ I, (F i ω) ^ α i) ≤
      ∏ i ∈ I, (finiteExpectation w (F i)) ^ α i := by
  have h := sum_geometric_holder I (fun i ω ↦ w ω * F i ω) α
    (fun i hi ω ↦ mul_nonneg (hw ω) (hF i hi ω)) hα hsum
  have hprod : ∀ ω, (∏ i ∈ I, (w ω * F i ω) ^ α i) = w ω * ∏ i ∈ I, (F i ω) ^ α i := by
    intro ω
    calc
      _ = ∏ i ∈ I, ((w ω) ^ α i * (F i ω) ^ α i) :=
        prod_congr rfl fun i hi ↦ Real.mul_rpow (hw ω) (hF i hi ω)
      _ = (∏ i ∈ I, (w ω) ^ α i) * ∏ i ∈ I, (F i ω) ^ α i := prod_mul_distrib
      _ = _ := by rw [← Real.rpow_sum_of_nonneg (hw ω) hα, hsum, Real.rpow_one]
  simpa only [hprod, finiteExpectation] using h

end PaperP1.FiniteHolder
