module

public import PaperP1.Diophantine.ActualIntegerSourceEquation
public import PaperP1.Diophantine.ZeroDegreeQuadraticFibres
public import PaperP1.Diophantine.ZeroDegreeLinearFibres

/-! # Literal source pairs satisfy the arithmetic fibre conditions -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ActualSourceArithmetic

open Finset PaperP1.TwoKernelDeterminantBoxes PaperP1.DeterminantSourceBox
open PaperP1.DeterminantSignedBoxes PaperP1.ActualProjectivePairs PaperP1.IntegralSourceCoefficients

theorem signed_population_height {N Q : ℕ} {ρ C δ : ℝ} (X : Box N ρ C δ)
    (h : ℤ) (S : Finset Quad) (hS : SignedPopulation X h S) (hQ : 2 * C ≤ (Q : ℝ)) :
    ∀ p ∈ S, p.1.1 ≤ Q * N ∧ p.1.2 ≤ Q * N ∧ p.2.1 ≤ Q * N ∧ p.2.2 ≤ Q * N := by
  have hfirst := DeterminantBoxScales.coordinate_bounds X.c₁_ge_one X.D_ge_one X.U_ge_one X.first_upper
  have hsecond := DeterminantBoxScales.coordinate_bounds X.c₂_ge_one X.E_ge_one X.V_ge_one X.second_upper
  have hscale := mul_le_mul_of_nonneg_right hQ (Nat.cast_nonneg N)
  intro p hp
  have hdR : (p.1.1 : ℝ) ≤ Q * N := by nlinarith only [(hS.d_bounds p hp).2, hfirst.2.1, hscale]
  have heR : (p.1.2 : ℝ) ≤ Q * N := by nlinarith only [(hS.e_bounds p hp).2, hsecond.2.1, hscale]
  have huR : (p.2.1 : ℝ) ≤ Q * N := by nlinarith only [(hS.u_bounds p hp).2, hfirst.2.2, hscale]
  have hvR : (p.2.2 : ℝ) ≤ Q * N := by nlinarith only [(hS.v_bounds p hp).2, hsecond.2.2, hscale]
  exact ⟨by exact_mod_cast hdR, by exact_mod_cast heR, by exact_mod_cast huR, by exact_mod_cast hvR⟩

theorem integerPoint_positive {N : ℕ} {ρ C δ : ℝ} {X : Box N ρ C δ} {h : ℤ}
    {S : Finset Quad} (hS : SignedPopulation X h S) (p : Quad) (hp : p ∈ S) :
    (∀ i, 0 < (integerPoint p).1 i) ∧ ∀ i, 0 < (integerPoint p).2 i := by
  have hd : (0 : ℤ) < (p.1.1 : ℤ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one (X.D_ge_one.trans (hS.d_bounds p hp).1))
  have he : (0 : ℤ) < (p.1.2 : ℤ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one (X.E_ge_one.trans (hS.e_bounds p hp).1))
  have hu : (0 : ℤ) < (p.2.1 : ℤ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one (X.U_ge_one.trans (hS.u_bounds p hp).1))
  have hv : (0 : ℤ) < (p.2.2 : ℤ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one (X.V_ge_one.trans (hS.v_bounds p hp).1))
  constructor
  · intro i
    fin_cases i
    · simpa [integerPoint] using hd
    · simpa [integerPoint] using he
  · intro i
    fin_cases i
    · simpa [integerPoint] using hv
    · simpa [integerPoint] using hu

theorem quadratic_valid {N H : ℕ} {ρ C δ : ℝ} {X : Box N ρ C δ} (coefs : IntegerCoefficients X)
    {h : ℤ} {S : Finset Quad} (hS : SignedPopulation X h S) (p : Quad) (hp : p ∈ S)
    (hprim : Primitive p) (hheight : p.1.1 ≤ H ∧ p.1.2 ≤ H ∧ p.2.1 ≤ H ∧ p.2.2 ≤ H) :
    ZeroDegreeQuadraticFibres.Valid coefs.c₁ coefs.c₂ h H (integerPoint p) := by
  have hpos := integerPoint_positive hS p hp
  refine ⟨hpos.1, hpos.2, ?_, ?_, (integerPoint_primitive p hprim).2, ?_⟩
  · intro i
    fin_cases i
    · simpa [integerPoint] using hheight.1
    · simpa [integerPoint] using hheight.2.1
  · intro i
    fin_cases i
    · simpa [integerPoint] using hheight.2.2.2
    · simpa [integerPoint] using hheight.2.2.1
  · have heq := ActualIntegerSourceEquation.source_value coefs h S hS p hp
    rwa [SourceBihomogeneousEquation.source_evaluation] at heq

theorem linear_valid {N : ℕ} {ρ C δ : ℝ} {X : Box N ρ C δ} (coefs : IntegerCoefficients X)
    {h : ℤ} {S : Finset Quad} (hS : SignedPopulation X h S) (p : Quad) (hp : p ∈ S) (hprim : Primitive p) :
    ZeroDegreeLinearFibres.Valid coefs.c₁ coefs.c₂ h (integerPoint p) := by
  have hpos := integerPoint_positive hS p hp
  refine ⟨hpos.1, hpos.2, (integerPoint_primitive p hprim).1, ?_⟩
  have heq := ActualIntegerSourceEquation.source_value coefs h S hS p hp
  rwa [SourceBihomogeneousEquation.source_evaluation] at heq

theorem uniform_polynomial_height (C : ℝ) (hC : 0 < C) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ ρ δ : ℝ, ∀ X : Box N ρ C δ,
      ∀ coefs : IntegerCoefficients X, ∀ h : ℤ, ∀ S : Finset Quad, SignedPopulation X h S →
        coefs.c₁ ≤ N ^ 2 ∧ coefs.c₂ ≤ N ^ 2 ∧
          ∀ p ∈ S, p.1.1 ≤ N ^ 2 ∧ p.1.2 ≤ N ^ 2 ∧ p.2.1 ≤ N ^ 2 ∧ p.2.2 ≤ N ^ 2 := by
  let Q := ⌈2 * C⌉₊ + 1
  have hQ : 1 ≤ Q := by dsimp [Q]; omega
  have hQR : 2 * C ≤ (Q : ℝ) := by
    have hh := Nat.le_ceil (2 * C)
    dsimp [Q]
    push_cast
    linarith
  refine ⟨Q, hQ, ?_⟩
  intro N hN ρ δ X coefs h S hS
  have hbound : Q * N ≤ N ^ 2 := by nlinarith
  have hc : C * (N : ℝ) ≤ Q * N := mul_le_mul_of_nonneg_right (by linarith : C ≤ (Q : ℝ)) (Nat.cast_nonneg N)
  have hcoeff := coefficient_upper coefs
  have h₁ : coefs.c₁ ≤ Q * N := by exact_mod_cast hcoeff.1.trans hc
  have h₂ : coefs.c₂ ≤ Q * N := by exact_mod_cast hcoeff.2.trans hc
  refine ⟨h₁.trans hbound, h₂.trans hbound, ?_⟩
  intro p hp
  have ht := signed_population_height X h S hS hQR p hp
  exact ⟨ht.1.trans hbound, ht.2.1.trans hbound, ht.2.2.1.trans hbound, ht.2.2.2.trans hbound⟩

end PaperP1.ActualSourceArithmetic
