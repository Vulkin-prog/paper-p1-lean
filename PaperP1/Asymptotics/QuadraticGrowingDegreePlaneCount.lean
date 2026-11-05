module

public import PaperP1.Arithmetic.QuadraticPlaneUniformBound

/-! # The complete unconditional growing-degree plane corollary with quadratic endpoint budget -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.QuadraticGrowingDegreePlaneCount

open Polynomial PlaneCurvePointCount

theorem source_uniform_bound (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∃ A : ℝ, 0 < A ∧ ∃ B₀ : ℕ, 2 ≤ B₀ ∧ ∀ B ≥ B₀, ∀ M : ℝ,
      ∀ (K : Type) [Field K] [CharZero K] [Algebra K ℂ], ∀ P : K[X][X], Irreducible P →
      2 ≤ PlaneCurvePointCount.degree P → (PlaneCurvePointCount.degree P : ℝ) ≤ M →
        ((grid P ⌊c₀ * B⌋₊).card : ℝ) ≤
          A * ((B : ℝ) ^ (1 / 2 : ℝ) + M ^ 2) * Real.log B ^ (17 : ℝ) := by
  obtain ⟨c, hc, hbound⟩ := QuadraticPlaneUniformBound.uniform_bound
  exact source_uniform_bound_under_BCN c 17 c₀ hc hc₀ hbound

theorem upper_power_cap (c₀ a : ℝ) (hc₀ : 0 < c₀) (ha : 0 ≤ a) (ha₁ : a < 1 / 2)
    (cap : ℕ → ℝ) (hcap : UpperPowerCap a cap) (ε : ℝ) (hε : 0 < ε) :
    ∃ B₀ : ℕ, 2 ≤ B₀ ∧ ∀ B ≥ B₀,
      ∀ (K : Type) [Field K] [CharZero K] [Algebra K ℂ], ∀ P : K[X][X], Irreducible P →
      2 ≤ PlaneCurvePointCount.degree P → (PlaneCurvePointCount.degree P : ℝ) ≤ cap B →
        ((grid P ⌊c₀ * B⌋₊).card : ℝ) ≤ ε * B := by
  obtain ⟨c, hc, hbound⟩ := QuadraticPlaneUniformBound.uniform_bound
  exact growing_degree_under_BCN c 17 c₀ a hc hc₀ ha ha₁ hbound cap hcap ε hε

theorem article_13_5 (c₀ a : ℝ) (hc₀ : 0 < c₀) (ha : 0 ≤ a) (ha₁ : a < 1 / 2)
    (cap : ℕ → ℝ) (hcap : UpperPowerCap a cap) :
    (∃ A : ℝ, 0 < A ∧ ∃ B₀ : ℕ, 2 ≤ B₀ ∧ ∀ B ≥ B₀,
      ∀ (K : Type) [Field K] [CharZero K] [Algebra K ℂ], ∀ P : K[X][X], Irreducible P →
      2 ≤ PlaneCurvePointCount.degree P → (PlaneCurvePointCount.degree P : ℝ) ≤ cap B →
        ((grid P ⌊c₀ * B⌋₊).card : ℝ) ≤
          A * ((B : ℝ) ^ (1 / 2 : ℝ) + cap B ^ 2) * Real.log B ^ (17 : ℝ)) ∧
    (∀ ε : ℝ, 0 < ε → ∃ B₀ : ℕ, 2 ≤ B₀ ∧ ∀ B ≥ B₀,
      ∀ (K : Type) [Field K] [CharZero K] [Algebra K ℂ], ∀ P : K[X][X], Irreducible P →
      2 ≤ PlaneCurvePointCount.degree P → (PlaneCurvePointCount.degree P : ℝ) ≤ cap B →
        ((grid P ⌊c₀ * B⌋₊).card : ℝ) ≤ ε * B) := by
  obtain ⟨c, hc, hbound⟩ := QuadraticPlaneUniformBound.uniform_bound
  exact article_13_5_under_BCN c 17 c₀ a hc hc₀ ha ha₁ hbound cap hcap

end PaperP1.QuadraticGrowingDegreePlaneCount
