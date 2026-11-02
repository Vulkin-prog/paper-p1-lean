module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.PowerSeries.Inverse

/-! # Actual formal lifting of a simple fibre root in the complete power-series ring -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PowerSeriesHenselLift

open Polynomial

theorem constantCoeff_eval {K : Type*} [Field K] (f : (PowerSeries K)[X]) (a : PowerSeries K) :
    PowerSeries.constantCoeff (f.eval a) =
      (f.map PowerSeries.constantCoeff).eval (PowerSeries.constantCoeff a) :=
  (Polynomial.eval_map_apply (f := PowerSeries.constantCoeff) (p := f) a).symm

theorem exists_root {K : Type*} [Field K] (f : (PowerSeries K)[X])
    (hlc : IsUnit f.leadingCoeff) (z : K)
    (hz : (f.map PowerSeries.constantCoeff).eval z = 0)
    (hdz : (f.map PowerSeries.constantCoeff).derivative.eval z ≠ 0) :
    ∃ y : PowerSeries K, f.eval y = 0 ∧ PowerSeries.constantCoeff y = z := by
  obtain ⟨v, hv⟩ := hlc
  let F : (PowerSeries K)[X] := C ((↑v⁻¹ : PowerSeries K)) * f
  have hmonic : F.Monic := by
    change (C ((↑v⁻¹ : PowerSeries K)) * f).leadingCoeff = 1
    rw [Polynomial.leadingCoeff_C_mul_of_isUnit (Units.isUnit v⁻¹), ← hv]
    simp
  have hfc : PowerSeries.constantCoeff (f.eval (PowerSeries.C z)) = 0 := by
    rw [constantCoeff_eval, PowerSeries.constantCoeff_C]
    exact hz
  have hFc : PowerSeries.constantCoeff (F.eval (PowerSeries.C z)) = 0 := by
    change PowerSeries.constantCoeff ((C ((↑v⁻¹ : PowerSeries K)) * f).eval (PowerSeries.C z)) = 0
    rw [Polynomial.eval_mul, Polynomial.eval_C, map_mul, hfc, mul_zero]
  have hmem : F.eval (PowerSeries.C z) ∈ Ideal.span {(PowerSeries.X : PowerSeries K)} := by
    rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]
    exact hFc
  have hdc : PowerSeries.constantCoeff (f.derivative.eval (PowerSeries.C z)) ≠ 0 := by
    rw [constantCoeff_eval, PowerSeries.constantCoeff_C, ← Polynomial.derivative_map]
    exact hdz
  have hdu : IsUnit (f.derivative.eval (PowerSeries.C z)) :=
    PowerSeries.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr hdc)
  have hFdu : IsUnit (F.derivative.eval (PowerSeries.C z)) := by
    change IsUnit ((C ((↑v⁻¹ : PowerSeries K)) * f).derivative.eval (PowerSeries.C z))
    rw [Polynomial.derivative_C_mul, Polynomial.eval_mul, Polynomial.eval_C]
    exact (Units.isUnit v⁻¹).mul hdu
  obtain ⟨y, hy, hmod⟩ := HenselianRing.is_henselian (R := PowerSeries K)
    (I := Ideal.span {(PowerSeries.X : PowerSeries K)}) F hmonic (PowerSeries.C z) hmem
    (hFdu.map (Ideal.Quotient.mk _))
  have hcy : PowerSeries.constantCoeff y = z := by
    rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff, map_sub, PowerSeries.constantCoeff_C, sub_eq_zero] at hmod
    exact hmod
  have hzero : (↑v⁻¹ : PowerSeries K) * f.eval y = 0 := by
    simpa only [F, Polynomial.IsRoot, Polynomial.eval_mul, Polynomial.eval_C] using hy
  exact ⟨y, (mul_eq_zero.mp hzero).resolve_left (Units.ne_zero v⁻¹), hcy⟩

end PaperP1.PowerSeriesHenselLift
