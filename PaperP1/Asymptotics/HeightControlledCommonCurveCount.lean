module

public import PaperP1.Arithmetic.HeightControlledCommonCurveGrid
public import PaperP1.Analysis.BinaryLogarithmicBudget
public import PaperP1.Asymptotics.HalfCountSchedule

/-! # Uniform normalized sublinear counts throughout the actual short-support range

The threshold precedes every support budget and every equation. Coefficient
height and the positive maximum partial degree remain explicit.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HeightControlledCommonCurveCount

open Polynomial BivariateDegrees BivariateHeight CurveIntegerFibres
  DegreeUniformAffineParameters HeightControlledCommonCurveGrid

theorem power_cap (a : ℝ) (ha : a < 1 / 2) (ε : ℝ) (hε : 0 < ε) :
    ∃ B₀ : ℕ, 2 ≤ B₀ ∧ ∀ B ≥ B₀, ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (B : ℝ) ^ a →
      ∀ G : ℤ[X][X], Irreducible G → 2 ≤ PlaneCurvePointCount.degree G →
      PlaneCurvePointCount.degree G ≤ 48 * q → height G ≤ (B + 1) ^ (2472 * q) →
        ((integerGrid G B).card : ℝ) /
          ((max (degreeX G) (degreeY G) : ℕ) : ℝ) ≤ ε * B := by
  obtain ⟨C, hC, hcount⟩ := normalized_count
  let m := max (2 * a) (a + 1 / 2)
  have hm : m < 1 := max_lt (by linarith only [ha]) (by linarith only [ha])
  let δ := (1 - m) / 2
  have hδ : 0 < δ := by dsimp only [δ]; linarith only [hm]
  have hs : δ + m < 1 := by dsimp only [δ]; linarith only [hm]
  obtain ⟨NL, _hNL, hlog⟩ := BinaryLogarithmicBudget.polynomial_absorption (2 * C) 2 δ hδ
  obtain ⟨ND, hd⟩ := HalfCountSchedule.factor_absorption 48 a (1 - a) (by linarith only [ha])
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (1 / ε) (δ + m) (1 - (δ + m))
    (by linarith only [hs])
  refine ⟨2 + NL + ND + NF, by omega, ?_⟩
  intro B hB q hq hcap G hG hD hDq hheight
  have hn : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hn1 : (1 : ℝ) ≤ B := by exact_mod_cast (show 1 ≤ B by omega)
  have hlinear : 48 * (B : ℝ) ^ a ≤ B := by
    have hh := hd B (by omega)
    simpa only [show a + (1 - a) = 1 by ring, Real.rpow_one] using hh
  have hDB : PlaneCurvePointCount.degree G ≤ B := by
    have hh : (PlaneCurvePointCount.degree G : ℝ) ≤ B := by
      have hdeg : (PlaneCurvePointCount.degree G : ℝ) ≤ 48 * q := by exact_mod_cast hDq
      nlinarith only [hdeg, hcap, hlinear]
    exact_mod_cast hh
  have hc := hcount B q (by omega) hq G hG hD hDB hDq hheight
  have hq2 : (q : ℝ) ^ 2 ≤ (B : ℝ) ^ m := by
    calc
      _ ≤ ((B : ℝ) ^ a) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hcap 2
      _ = (B : ℝ) ^ (2 * a) := by rw [← Real.rpow_mul_natCast hn.le]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (le_max_left _ _)
  have hqR : (q : ℝ) * (B : ℝ) ^ (1 / 2 : ℝ) ≤ (B : ℝ) ^ m := by
    calc
      _ ≤ (B : ℝ) ^ a * (B : ℝ) ^ (1 / 2 : ℝ) := mul_le_mul_of_nonneg_right hcap (by positivity)
      _ = (B : ℝ) ^ (a + 1 / 2) := (Real.rpow_add hn _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (le_max_right _ _)
  have hcoef : 2 * C * (logarithmicBudget B : ℝ) ^ 2 ≤ (B : ℝ) ^ δ :=
    (le_abs_self _).trans (hlog B (by omega))
  have hprofile : C * profile q B ≤ (B : ℝ) ^ (δ + m) := by
    calc
      _ ≤ C * (2 * (B : ℝ) ^ m) * (logarithmicBudget B : ℝ) ^ 2 := by
        unfold profile
        rw [← mul_assoc]
        gcongr
        linarith only [hq2, hqR]
      _ = (2 * C * (logarithmicBudget B : ℝ) ^ 2) * (B : ℝ) ^ m := by ring
      _ ≤ (B : ℝ) ^ δ * (B : ℝ) ^ m := mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ = _ := (Real.rpow_add hn _ _).symm
  have hfinal := hf B (by omega)
  rw [show δ + m + (1 - (δ + m)) = 1 by ring, Real.rpow_one] at hfinal
  have hquot : (B : ℝ) ^ (δ + m) / ε ≤ B := by
    simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul, mul_one] using hfinal
  have hh := (div_le_iff₀ hε).mp hquot
  exact (hc.trans hprofile).trans (by simpa only [mul_comm] using hh)

end PaperP1.HeightControlledCommonCurveCount
