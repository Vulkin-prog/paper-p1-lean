module

public import PaperP1.Analysis.DeterminantFixedInflation

/-! # Literal original source-box parameters and their actual finite solution populations -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DeterminantSourceBox

open Finset PaperP1.TwoKernelDeterminantBoxes

structure Box (N : ℕ) (ρ C δ : ℝ) where
  c₁ : ℝ
  c₂ : ℝ
  D : ℝ
  E : ℝ
  U : ℝ
  V : ℝ
  c₁_ge_one : 1 ≤ c₁
  c₂_ge_one : 1 ≤ c₂
  D_ge_one : 1 ≤ D
  E_ge_one : 1 ≤ E
  U_ge_one : 1 ≤ U
  V_ge_one : 1 ≤ V
  first_lower : ρ * N ≤ c₁ * D ^ 2 * U
  first_upper : c₁ * D ^ 2 * U ≤ C * N
  second_lower : ρ * N ≤ c₂ * E ^ 2 * V
  second_upper : c₂ * E ^ 2 * V ≤ C * N
  first_log : δ * Real.log N ≤ Real.log (D * E)
  second_log : δ * Real.log N ≤ Real.log (U * V)

structure Population {N : ℕ} {ρ C δ : ℝ} (X : Box N ρ C δ) (h : ℕ) (S : Finset Quad) : Prop where
  d_bounds : ∀ p ∈ S, X.D ≤ p.1.1 ∧ (p.1.1 : ℝ) ≤ 2 * X.D
  e_bounds : ∀ p ∈ S, X.E ≤ p.1.2 ∧ (p.1.2 : ℝ) ≤ 2 * X.E
  u_bounds : ∀ p ∈ S, X.U ≤ p.2.1 ∧ (p.2.1 : ℝ) ≤ 2 * X.U
  v_bounds : ∀ p ∈ S, X.V ≤ p.2.2 ∧ (p.2.2 : ℝ) ≤ 2 * X.V
  equation : ∀ p ∈ S, X.c₂ * (p.1.2 : ℝ) ^ 2 * p.2.2 = X.c₁ * (p.1.1 : ℝ) ^ 2 * p.2.1 + h

theorem population_height {N h Q : ℕ} {ρ C δ : ℝ} (X : Box N ρ C δ) (S : Finset Quad)
    (hS : Population X h S) (hQ : 2 * C ≤ (Q : ℝ)) :
    ∀ p ∈ S, p.1.1 ≤ Q * N ∧ p.1.2 ≤ Q * N ∧ p.2.1 ≤ Q * N ∧ p.2.2 ≤ Q * N := by
  have hfirst := DeterminantBoxScales.coordinate_bounds X.c₁_ge_one X.D_ge_one X.U_ge_one X.first_upper
  have hsecond := DeterminantBoxScales.coordinate_bounds X.c₂_ge_one X.E_ge_one X.V_ge_one X.second_upper
  have hscale := mul_le_mul_of_nonneg_right hQ (Nat.cast_nonneg N)
  intro p hp
  have hd := (hS.d_bounds p hp).2
  have he := (hS.e_bounds p hp).2
  have hu := (hS.u_bounds p hp).2
  have hv := (hS.v_bounds p hp).2
  have hdR : (p.1.1 : ℝ) ≤ Q * N := by nlinarith only [hd, hfirst.2.1, hscale]
  have heR : (p.1.2 : ℝ) ≤ Q * N := by nlinarith only [he, hsecond.2.1, hscale]
  have huR : (p.2.1 : ℝ) ≤ Q * N := by nlinarith only [hu, hfirst.2.2, hscale]
  have hvR : (p.2.2 : ℝ) ≤ Q * N := by nlinarith only [hv, hsecond.2.2, hscale]
  exact ⟨by exact_mod_cast hdR, by exact_mod_cast heR, by exact_mod_cast huR, by exact_mod_cast hvR⟩

theorem population_denominators_positive {N h : ℕ} {ρ C δ : ℝ} (X : Box N ρ C δ)
    (S : Finset Quad) (hS : Population X h S) (p : Quad) (hp : p ∈ S) :
    0 < p.1.2 ∧ 0 < p.2.1 := by
  have he : (1 : ℝ) ≤ p.1.2 := X.E_ge_one.trans (hS.e_bounds p hp).1
  have hu : (1 : ℝ) ≤ p.2.1 := X.U_ge_one.trans (hS.u_bounds p hp).1
  constructor
  · have hh : 1 ≤ p.1.2 := by exact_mod_cast he
    omega
  · have hh : 1 ≤ p.2.1 := by exact_mod_cast hu
    omega

theorem population_source_lower {N h : ℕ} {ρ C δ : ℝ} (X : Box N ρ C δ)
    (S : Finset Quad) (hS : Population X h S) (p : Quad) (hp : p ∈ S) :
    ρ * N ≤ DeterminantRelativeChart.source X.c₁ p.1.1 p.2.1 := by
  have hc : 0 ≤ X.c₁ := by linarith only [X.c₁_ge_one]
  have hd : 0 ≤ X.D := by linarith only [X.D_ge_one]
  have hu : 0 ≤ X.U := by linarith only [X.U_ge_one]
  have hpow := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hd (hS.d_bounds p hp).1 2) hc
  have hprod := mul_le_mul hpow (hS.u_bounds p hp).1 hu
    (mul_nonneg hc (sq_nonneg (p.1.1 : ℝ)))
  exact X.first_lower.trans hprod

end PaperP1.DeterminantSourceBox
