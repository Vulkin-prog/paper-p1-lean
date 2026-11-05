module

public import PaperP1.Arithmetic.FixedDegreeSharpFieldPlaneCount
public import PaperP1.Asymptotics.BoundedDegreePlaneCounts
public import PaperP1.Algebra.BivariateFactorDegree

/-! # Unconditional square-root counts on every fixed finite plane-degree range

The fixed degree ceiling and box dilation precede the height, field and equation.
No degree-uniform BCN property is assumed.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BoundedPlaneCurveCount

open Polynomial Finset BivariateFactorDegree

theorem field_uniform_bound (D K : ℕ) (hK : 1 ≤ K) (δ : ℝ) (hδ : 0 < δ) :
    ∃ B₀ : ℕ, 2 ≤ B₀ ∧ ∀ B ≥ B₀, ∀ (F : Type*) [Field F] [CharZero F], ∀ P : F[X][X],
      Irreducible P → 2 ≤ PlaneCurvePointCount.degree P → PlaneCurvePointCount.degree P ≤ D →
        ((PlaneCurvePointCount.grid P (K * B)).card : ℝ) ≤ (B : ℝ) ^ ((1 : ℝ) / 2 + δ) := by
  obtain ⟨A, hA, hcount⟩ := FixedDegreeSharpFieldPlaneCount.bounded_degree_count D (δ / 2) (by positivity)
  let C := A * (K : ℝ) ^ ((1 : ℝ) / 2 + δ / 2)
  obtain ⟨H₀, hH₀, hsmall⟩ := BoundedDegreePlaneCounts.eventual_power_absorption C
    ((1 : ℝ) / 2 + δ / 2) ((1 : ℝ) / 2 + δ) (by linarith)
  refine ⟨max 2 ⌈H₀⌉₊, by omega, ?_⟩
  intro B hB F _hF _hchar P hP hD hcap
  have hBH : H₀ ≤ (B : ℝ) := (Nat.le_ceil H₀).trans (by exact_mod_cast (show ⌈H₀⌉₊ ≤ B by omega))
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hKB : (B : ℝ) ≤ (K : ℝ) * B := le_mul_of_one_le_left hBpos.le hKR
  have hH : 2 < (K : ℝ) * B := (hH₀.trans_le hBH).trans_le hKB
  have hb := hcount F P hD hcap hP ((K : ℝ) * B) hH
  have hfloor : ⌊(K : ℝ) * B⌋₊ = K * B := by rw [← Nat.cast_mul, Nat.floor_natCast]
  rw [hfloor] at hb
  have hhalf : 1 / (PlaneCurvePointCount.degree P : ℝ) ≤ (1 : ℝ) / 2 :=
    one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hD)
  have hpow : ((K : ℝ) * B) ^ (1 / (PlaneCurvePointCount.degree P : ℝ) + δ / 2) ≤
      ((K : ℝ) * B) ^ ((1 : ℝ) / 2 + δ / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  calc
    _ ≤ A * ((K : ℝ) * B) ^ (1 / (PlaneCurvePointCount.degree P : ℝ) + δ / 2) := hb
    _ ≤ A * ((K : ℝ) * B) ^ ((1 : ℝ) / 2 + δ / 2) := mul_le_mul_of_nonneg_left hpow hA
    _ = C * (B : ℝ) ^ ((1 : ℝ) / 2 + δ / 2) := by
      dsimp only [C]
      rw [Real.mul_rpow (Nat.cast_nonneg K) (Nat.cast_nonneg B)]
      ring
    _ ≤ _ := hsmall (B : ℝ) hBH

theorem uniform_bound (D K : ℕ) (hK : 1 ≤ K) (δ : ℝ) (hδ : 0 < δ) :
    ∃ B₀ : ℕ, 2 ≤ B₀ ∧ ∀ B ≥ B₀, ∀ P : ℚ[X][X], Irreducible P →
      2 ≤ totalDegree P → degreeSum P ≤ D →
      ((PlaneCurvePointCount.grid P (K * B)).card : ℝ) ≤ (B : ℝ) ^ ((1 : ℝ) / 2 + δ) := by
  obtain ⟨B₀, hB₀, hcount⟩ := field_uniform_bound D K hK δ hδ
  refine ⟨B₀, hB₀, ?_⟩
  intro B hB P hP hD hcap
  exact hcount B hB ℚ P hP hD ((totalDegree_le_degreeSum P).trans hcap)

end PaperP1.BoundedPlaneCurveCount
