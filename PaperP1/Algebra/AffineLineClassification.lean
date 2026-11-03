module

public import PaperP1.Algebra.NativeVeroneseLineChart
public import PaperP1.Algebra.NativeVeroneseVerticalChart
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-! # A nonzero affine linear equation through a point is a graph line or its vertical line -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AffineLineClassification

open Polynomial

variable {F : Type*} [Field F]

def linear (a b c : F) : F[X][X] := C (C a) * X + C (C b * X) + C (C c)

def valueMap (x y : F) : F[X][X] →+* F := eval₂RingHom (evalRingHom x) y

theorem value_linear (a b c x y : F) : valueMap x y (linear a b c) = a * y + b * x + c := by
  simp [valueMap, linear]

theorem classify (a b c x y : F) (hcoeff : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0)
    (hzero : a * y + b * x + c = 0) :
    (∃ α β : F, Ideal.span {linear a b c} = Ideal.span {NativeVeroneseLineChart.equation α β} ∧
      y = α * x + β) ∨
    Ideal.span {linear a b c} = Ideal.span {NativeVeroneseVerticalChart.equation x} := by
  by_cases ha : a = 0
  · right
    have hb : b ≠ 0 := by
      intro hb
      have hc : c = 0 := by simpa only [ha, hb, zero_mul, zero_add] using hzero
      exact hcoeff.elim (fun h ↦ h ha) (fun h ↦ h.elim (fun h ↦ h hb) (fun h ↦ h hc))
    have hc : c = -(b * x) := by
      have h : b * x + c = 0 := by simpa only [ha, zero_mul, zero_add] using hzero
      exact eq_neg_of_add_eq_zero_right h
    have he : linear a b c = C (C b) * NativeVeroneseVerticalChart.equation x := by
      simp only [linear, ha, hc, C_0, zero_mul, zero_add, NativeVeroneseVerticalChart.equation,
        C_sub, C_mul, C_neg]
      ring
    rw [he]
    exact Ideal.span_singleton_mul_left_unit ((isUnit_iff_ne_zero.mpr hb).map C |>.map C) _
  · left
    have hb : a * (-b / a) = -b := by field_simp
    have hc : a * (-c / a) = -c := by field_simp
    refine ⟨-b / a, -c / a, ?_, ?_⟩
    · have hB : C (C a) * C (C (-b / a)) = -C (C b) := by
        rw [← C_mul, ← C_mul, hb, C_neg, C_neg]
      have hC : C (C a) * C (C (-c / a)) = -C (C c) := by
        rw [← C_mul, ← C_mul, hc, C_neg, C_neg]
      have he : linear a b c = C (C a) * NativeVeroneseLineChart.equation (-b / a) (-c / a) := by
        simp only [linear, NativeVeroneseLineChart.equation, C_add, C_mul, mul_sub, mul_add]
        rw [← mul_assoc, hB, hC]
        ring
      rw [he]
      exact Ideal.span_singleton_mul_left_unit ((isUnit_iff_ne_zero.mpr ha).map C |>.map C) _
    · apply mul_left_cancel₀ ha
      calc
        a * y = -(b * x + c) := eq_neg_of_add_eq_zero_left (by simpa only [add_assoc] using hzero)
        _ = a * (-b / a * x + -c / a) := by
          rw [mul_add, ← mul_assoc, hb, hc]
          ring

end PaperP1.AffineLineClassification
