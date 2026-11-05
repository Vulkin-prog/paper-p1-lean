module

public import PaperP1.Arithmetic.LinearPlaneGridBound
public import PaperP1.Arithmetic.IntegerCurveRationalization

/-! # Reducing the open plane estimate to geometric equations of degree at least two

`Input` remains an ordinary unproved argument. Linear equations and all
non-geometric equations are counted internally, with an explicit enlargement
of the uniform constant. No BCN theorem is asserted by this reduction.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GeometricPlanePointInput

open Polynomial PaperP1.CurveDegreeProfile PaperP1.PolynomialScalarProjection

def Input (c κ : ℝ) : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] [Algebra K ℂ], ∀ P : K[X][X], Irreducible P →
    Irreducible (extend P : ℂ[X][X]) → 2 ≤ PlaneCurvePointCount.degree P →
      ∀ H : ℝ, 2 < H → ((PlaneCurvePointCount.grid P ⌊H⌋₊).card : ℝ) ≤
        c * profile H (PlaneCurvePointCount.degree P : ℝ) * Real.log H ^ κ

def constant (c κ : ℝ) : ℝ := max c (3 * (Real.log 2 ^ κ)⁻¹)

theorem constant_pos (c κ : ℝ) : 0 < constant c κ := by
  have hp : 0 < Real.log 2 ^ κ := Real.rpow_pos_of_pos (Real.log_pos (by norm_num)) κ
  exact lt_of_lt_of_le (mul_pos (by norm_num) (inv_pos.mpr hp)) (le_max_right _ _)

theorem logarithmic_budget (c κ H : ℝ) (hκ : 0 ≤ κ) (hH : 2 < H) :
    3 ≤ constant c κ * Real.log H ^ κ := by
  have hp : 0 < Real.log 2 ^ κ := Real.rpow_pos_of_pos (Real.log_pos (by norm_num)) κ
  have hl : Real.log 2 ≤ Real.log H := Real.log_le_log (by norm_num) hH.le
  have hpow := Real.rpow_le_rpow (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)) hl hκ
  calc
    3 = (3 * (Real.log 2 ^ κ)⁻¹) * Real.log 2 ^ κ := by
      rw [mul_assoc, inv_mul_cancel₀ hp.ne', mul_one]
    _ ≤ constant c κ * Real.log H ^ κ :=
      mul_le_mul (le_max_right _ _) hpow hp.le (constant_pos c κ).le

theorem nongeometric_bound (c κ : ℝ) (hκ : 0 ≤ κ)
    (K : Type) [Field K] [CharZero K] [Algebra K ℂ] (P : K[X][X]) (hP : Irreducible P)
    (hred : ¬Irreducible (extend P : ℂ[X][X])) (H : ℝ) (hH : 2 < H) :
    ((PlaneCurvePointCount.grid P ⌊H⌋₊).card : ℝ) ≤
      constant c κ * profile H (PlaneCurvePointCount.degree P : ℝ) * Real.log H ^ κ := by
  have hc := (NonGeometricPlanePointBound.grid_card P hP hred ⌊H⌋₊).trans
    (Nat.mul_le_mul_left (PlaneCurvePointCount.degree P) (Nat.sub_le _ 1))
  have hcr : ((PlaneCurvePointCount.grid P ⌊H⌋₊).card : ℝ) ≤
      (PlaneCurvePointCount.degree P : ℝ) * (PlaneCurvePointCount.degree P : ℝ) := by
    exact_mod_cast hc
  have hp : (PlaneCurvePointCount.degree P : ℝ) ^ 2 ≤
      profile H (PlaneCurvePointCount.degree P : ℝ) := by
    unfold profile
    exact le_mul_of_one_le_right (sq_nonneg _) (Real.one_le_rpow (by linarith)
      (one_div_nonneg.mpr (Nat.cast_nonneg _)))
  have hprof : 0 ≤ profile H (PlaneCurvePointCount.degree P : ℝ) := by
    unfold profile
    positivity
  have hnorm : 1 ≤ constant c κ * Real.log H ^ κ :=
    (by norm_num : (1 : ℝ) ≤ 3).trans (logarithmic_budget c κ H hκ hH)
  calc
    ((PlaneCurvePointCount.grid P ⌊H⌋₊).card : ℝ) ≤
        (PlaneCurvePointCount.degree P : ℝ) ^ 2 := by simpa only [pow_two] using hcr
    _ ≤ profile H (PlaneCurvePointCount.degree P : ℝ) := hp
    _ ≤ profile H (PlaneCurvePointCount.degree P : ℝ) * (constant c κ * Real.log H ^ κ) :=
      le_mul_of_one_le_right hprof hnorm
    _ = _ := by ring

theorem field_input (c κ : ℝ) (hκ : 0 ≤ κ) (hGeo : Input c κ) :
    PlaneCurvePointCount.UniformBound (constant c κ) κ := by
  intro K _hK _hchar _halg P hP hD H hH
  by_cases hd : PlaneCurvePointCount.degree P = 1
  · have hb := LinearPlaneGridBound.linear_real_grid_card P hP hd H hH
    have hn := logarithmic_budget c κ H hκ hH
    have hm := mul_le_mul_of_nonneg_left hn (by linarith : (0 : ℝ) ≤ H)
    have hp : profile H (PlaneCurvePointCount.degree P : ℝ) = H := by
      simp [profile, hd]
    rw [hp]
    nlinarith
  · by_cases hg : Irreducible (extend P : ℂ[X][X])
    · have hb := hGeo K P hP hg (by omega) H hH
      have hp : 0 ≤ profile H (PlaneCurvePointCount.degree P : ℝ) := by
        unfold profile
        positivity
      exact hb.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hp)
        (Real.rpow_nonneg (Real.log_nonneg (by linarith)) κ))
    · exact nongeometric_bound c κ hκ K P hP hg H hH

theorem integer_input (c κ : ℝ) (hκ : 0 ≤ κ) (hGeo : Input c κ) :
    IntegerCurvePointInput.UniformBound (constant c κ) κ :=
  IntegerCurveRationalization.integer_input_of_field_input _ _ (field_input c κ hκ hGeo)

theorem restriction_of_field_input (c κ : ℝ) (hBCN : PlaneCurvePointCount.UniformBound c κ) :
    Input c κ := by
  intro K _hK _hchar _halg P hP _hgeom hD H hH
  exact hBCN K P hP (by omega) H hH

end PaperP1.GeometricPlanePointInput
