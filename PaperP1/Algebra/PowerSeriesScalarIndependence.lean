module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-! # Scalar independence remains exact for finite power-series combinations

This is the coefficientwise separation needed to descend an extension-field
factor evaluated on a formal branch over the original field.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PowerSeriesScalarIndependence

open Finset

variable {K L ι : Type*} [Field K] [Field L] [Algebra K L]

theorem finite_sum_eq_zero_iff (b : ι → L) (hb : LinearIndependent K b)
    (s : Finset ι) (f : ι → PowerSeries K) :
    (∑ i ∈ s, PowerSeries.C (b i) * PowerSeries.map (algebraMap K L) (f i)) = 0 ↔
      ∀ i ∈ s, f i = 0 := by
  classical
  constructor
  · intro h i hi
    apply PowerSeries.ext
    intro n
    have hc := congrArg (fun z : PowerSeries L ↦ PowerSeries.coeff n z) h
    simp only [map_sum, PowerSeries.coeff_C_mul, PowerSeries.coeff_map, map_zero] at hc
    have hs : (∑ j ∈ s, PowerSeries.coeff n (f j) • b j) = 0 := by
      simpa only [Algebra.smul_def, mul_comm] using hc
    have hz := (linearIndependent_iff'.mp hb) s (fun j ↦ PowerSeries.coeff n (f j)) hs i hi
    simpa only [map_zero] using hz
  · intro h
    apply sum_eq_zero
    intro i hi
    rw [h i hi, map_zero, mul_zero]

theorem finite_sum_eq_iff (b : ι → L) (hb : LinearIndependent K b)
    (s : Finset ι) (f g : ι → PowerSeries K) :
    (∑ i ∈ s, PowerSeries.C (b i) * PowerSeries.map (algebraMap K L) (f i)) =
      (∑ i ∈ s, PowerSeries.C (b i) * PowerSeries.map (algebraMap K L) (g i)) ↔
        ∀ i ∈ s, f i = g i := by
  classical
  have heq : (∑ i ∈ s, PowerSeries.C (b i) *
      PowerSeries.map (algebraMap K L) (f i - g i)) =
        (∑ i ∈ s, PowerSeries.C (b i) * PowerSeries.map (algebraMap K L) (f i)) -
          (∑ i ∈ s, PowerSeries.C (b i) * PowerSeries.map (algebraMap K L) (g i)) := by
    simp only [map_sub, mul_sub, sum_sub_distrib]
  constructor
  · intro h
    have hz : (∑ i ∈ s, PowerSeries.C (b i) *
        PowerSeries.map (algebraMap K L) (f i - g i)) = 0 := by rw [heq, h, sub_self]
    have hh := (finite_sum_eq_zero_iff b hb s (fun i ↦ f i - g i)).mp hz
    intro i hi
    exact sub_eq_zero.mp (hh i hi)
  · intro h
    exact sum_congr rfl (fun i hi ↦ by rw [h i hi])

end PaperP1.PowerSeriesScalarIndependence
