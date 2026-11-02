module

public import PaperP1.Arithmetic.PlaneCurvePointCount

/-! # The explicit integer-polynomial specialization still required from BCN

`UniformBound` is an ordinary theorem argument. Neither BCN nor the rational
presentation/Gauss bridge from the separate field-polynomial input is proved here.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IntegerCurvePointInput

open Polynomial Filter PaperP1.BivariateTotalDegree PaperP1.CurveIntegerFibres
  PaperP1.CurveDegreeProfile PaperP1.CurveDegreeAsymptotics PaperP1.PlaneCurvePointCount

local instance : CommRing ℤ[X][X] := inferInstance

def UniformBound (c κ : ℝ) : Prop :=
  ∀ P : ℤ[X][X], Irreducible P → 0 < totalDegree P → ∀ H : ℝ, 2 < H →
    ((integerGrid P ⌊H⌋₊).card : ℝ) ≤ c * profile H (totalDegree P : ℝ) * Real.log H ^ κ

theorem constant_power_cap (A b : ℝ) : UpperPowerCap b (fun B : ℕ ↦ A * (B : ℝ) ^ b) := by
  intro δ hδ
  have hp := ((tendsto_rpow_atTop hδ).comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
    (eventually_ge_atTop A)
  obtain ⟨B₁, hB₁⟩ := eventually_atTop.mp hp
  refine ⟨max B₁ 1, ?_⟩
  intro B hB
  have hBp : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  calc
    A * (B : ℝ) ^ b ≤ (B : ℝ) ^ δ * (B : ℝ) ^ b :=
      mul_le_mul_of_nonneg_right (hB₁ B (by omega)) (Real.rpow_nonneg hBp.le b)
    _ = (B : ℝ) ^ (b + δ) := by rw [← Real.rpow_add hBp]; congr 1; ring

theorem growing_degree_under_BCN (c κ c₀ a : ℝ) (hc : 0 < c) (hc₀ : 0 < c₀)
    (ha : 0 ≤ a) (ha₁ : a < 1 / 2) (hBCN : UniformBound c κ)
    (cap : ℕ → ℝ) (hcap : UpperPowerCap a cap) (ε : ℝ) (hε : 0 < ε) :
    ∃ B₀ : ℕ, 2 ≤ B₀ ∧ ∀ B ≥ B₀, ∀ P : ℤ[X][X], Irreducible P →
      2 ≤ totalDegree P → (totalDegree P : ℝ) ≤ cap B →
        ((integerGrid P ⌊c₀ * B⌋₊).card : ℝ) ≤ ε * B := by
  let δ : ℝ := (1 / 2 - a) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨Bcap, hBcap⟩ := hcap δ hδ
  obtain ⟨Bprofile, hBprofile, hprofile⟩ := uniform_sublinear c₀ (a + δ) κ hc₀
    (by linarith) (by dsimp [δ]; linarith) (ε / c) (div_pos hε hc)
  obtain ⟨Bheight, hBheight, hheight⟩ := logarithmic_weights_eventually c₀ κ hc₀
  refine ⟨max Bcap (max Bprofile Bheight), by omega, ?_⟩
  intro B hB P hP hD hDM
  have hH := (hheight B (by omega)).1
  have hbound := hBCN P hP (by omega) (c₀ * B) hH
  have hsmall := hprofile B (by omega) (totalDegree P : ℝ) (by exact_mod_cast hD)
    (hDM.trans (hBcap B (by omega)))
  calc
    ((integerGrid P ⌊c₀ * B⌋₊).card : ℝ) ≤
        c * (profile (c₀ * B) (totalDegree P : ℝ) * Real.log (c₀ * B) ^ κ) := by
      simpa only [mul_assoc] using hbound
    _ ≤ c * ((ε / c) * B) := mul_le_mul_of_nonneg_left hsmall hc.le
    _ = ε * B := by field_simp

theorem fixed_power_degree_under_BCN (c κ b A : ℝ) (hc : 0 < c)
    (hb : 0 ≤ b) (hb₁ : b < 1 / 2) (hBCN : UniformBound c κ) (ε : ℝ) (hε : 0 < ε) :
    ∃ B₀ : ℕ, 2 ≤ B₀ ∧ ∀ B ≥ B₀, ∀ P : ℤ[X][X], Irreducible P →
      2 ≤ totalDegree P → (totalDegree P : ℝ) ≤ A * (B : ℝ) ^ b →
        ((integerGrid P B).card : ℝ) ≤ ε * B := by
  obtain ⟨B₀, hB₀, hbound⟩ := growing_degree_under_BCN c κ 1 b hc (by norm_num) hb hb₁ hBCN
    (fun B : ℕ ↦ A * (B : ℝ) ^ b) (constant_power_cap A b) ε hε
  refine ⟨B₀, hB₀, ?_⟩
  intro B hB P hP hD hDM
  simpa only [one_mul, Nat.floor_natCast] using hbound B hB P hP hD hDM

end PaperP1.IntegerCurvePointInput
