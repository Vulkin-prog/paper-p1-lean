module

public import PaperP1.Arithmetic.PlaneCurvePointCount
public import PaperP1.Algebra.BivariateFactorDegree

/-! # The existing explicit BCN input gives every fixed-degree square-root point count

This is a bounded-degree specialization of an existing unproved input. No new
geometric property is assumed, and no unconditional BCN theorem is asserted.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BoundedPlaneCurveCountUnderBCN

open Filter Polynomial PaperP1.BivariateFactorDegree

theorem uniform_bound (c κ : ℝ) (hc : 0 < c) (hBCN : PlaneCurvePointCount.UniformBound c κ)
    (D K : ℕ) (hK : 1 ≤ K) (δ : ℝ) (hδ : 0 < δ) :
    ∃ B₀ : ℕ, 2 ≤ B₀ ∧ ∀ B ≥ B₀, ∀ P : ℚ[X][X], Irreducible P →
      2 ≤ totalDegree P → degreeSum P ≤ D →
      ((PlaneCurvePointCount.grid P (K * B)).card : ℝ) ≤ (B : ℝ) ^ (1 / 2 + δ) := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  obtain ⟨A, hA, NC, _hNC, hc₀⟩ := PlaneCurvePointCount.source_uniform_bound_under_BCN
    c κ (K : ℝ) hc hKR hBCN
  let a : ℝ := A * (1 + (D : ℝ) ^ 2)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hlim := ((PNT.tendsto_pow_log_div_pow_atTop δ κ hδ).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul a
  obtain ⟨NP, hp⟩ := eventually_atTop.mp (hlim.eventually
    (eventually_lt_nhds (show a * (0 : ℝ) < 1 by simp)))
  refine ⟨max 2 (max NC NP), by omega, ?_⟩
  intro B hB P hP hdegree hcap
  have hb : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hb1 : (1 : ℝ) ≤ B := by exact_mod_cast (show 1 ≤ B by omega)
  have hlog : 0 ≤ Real.log (B : ℝ) ^ κ := Real.rpow_nonneg (Real.log_nonneg hb1) κ
  have hhalf : (1 : ℝ) ≤ (B : ℝ) ^ (1 / 2 : ℝ) := Real.one_le_rpow hb1 (by norm_num)
  have hsmall : a * Real.log (B : ℝ) ^ κ ≤ (B : ℝ) ^ δ := by
    have hh := (hp B (by omega)).le
    change a * (Real.log (B : ℝ) ^ κ / (B : ℝ) ^ δ) ≤ 1 at hh
    rw [← mul_div_assoc] at hh
    exact (div_le_one (Real.rpow_pos_of_pos hb δ)).mp hh
  have hcap' : (PlaneCurvePointCount.degree P : ℝ) ≤ D := by
    exact_mod_cast (totalDegree_le_degreeSum P).trans hcap
  have hbound := hc₀ B (by omega) (D : ℝ) ℚ P hP hdegree hcap'
  have hfloor : ⌊(K : ℝ) * B⌋₊ = K * B := by rw [← Nat.cast_mul, Nat.floor_natCast]
  rw [hfloor] at hbound
  calc
    _ ≤ A * ((B : ℝ) ^ (1 / 2 : ℝ) + (D : ℝ) ^ 2) * Real.log B ^ κ := hbound
    _ ≤ (B : ℝ) ^ (1 / 2 : ℝ) * (a * Real.log B ^ κ) := by
      dsimp [a]
      have hh : (B : ℝ) ^ (1 / 2 : ℝ) + (D : ℝ) ^ 2 ≤
          (1 + (D : ℝ) ^ 2) * (B : ℝ) ^ (1 / 2 : ℝ) := by nlinarith only [hhalf, sq_nonneg (D : ℝ)]
      have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh hA.le) hlog
      nlinarith only [hm]
    _ ≤ (B : ℝ) ^ (1 / 2 : ℝ) * (B : ℝ) ^ δ := mul_le_mul_of_nonneg_left hsmall (by positivity)
    _ = _ := (Real.rpow_add hb _ _).symm

end PaperP1.BoundedPlaneCurveCountUnderBCN
