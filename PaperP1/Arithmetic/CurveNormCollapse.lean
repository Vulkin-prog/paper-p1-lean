module

public import PaperP1.Arithmetic.BiquadraticWordNorm

/-! # Primitive norm polynomials force square-class dependence after specialization -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CurveNormCollapse

open Finset Polynomial PaperP1.FormalWordPolynomials PaperP1.BiquadraticWordNorm
  PaperP1.BiquadraticSourceNorm
open scoped symmDiff

theorem source_dependence {F : Type*} [Field F] [CharZero F] (f₁ f₂ f₃ h g a b c d : F)
    (hg : g ≠ 0) (h₃ : f₃ * g ^ 2 = f₁ * f₂) (hh : h * g = f₂)
    (hne : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 ∨ d ≠ 0)
    (hz : sourceNorm f₁ f₂ f₃ h a b c d = 0) :
    IsSquare f₁ ∨ IsSquare f₂ ∨ IsSquare (f₁ * f₂) := by
  by_contra hn
  push Not at hn
  exact sourceNorm_ne_zero f₁ f₂ f₃ h g a b c d hg h₃ hh hn.1 hn.2.1 hn.2.2 hne hz

theorem overlap_ne_zero {F : Type*} [Field F] (φ : ℤ[X][X] →+* F) (I J K L : Finset ℤ)
    (h₁ : φ (wordOver ℤ I J) ≠ 0) (h₂ : φ (wordOver ℤ K L) ≠ 0) :
    φ (wordOver ℤ (I ∩ K) (J ∩ L)) ≠ 0 := by
  intro hG
  have h := congrArg φ (word_overlap ℤ I J K L)
  simp only [map_mul, map_pow, hG, zero_pow (by decide : 2 ≠ 0), mul_zero] at h
  exact mul_ne_zero h₁ h₂ h

theorem word_dependence {F : Type*} [Field F] [CharZero F] (φ : ℤ[X][X] →+* F)
    (I J K L : Finset ℤ) (A : Fin 4 → ℤ[X][X])
    (h₁ : φ (wordOver ℤ I J) ≠ 0) (h₂ : φ (wordOver ℤ K L) ≠ 0)
    (hA : ∃ χ, φ (A χ) ≠ 0) (hR : φ (normPolynomial I J K L A) = 0) :
    IsSquare (φ (wordOver ℤ I J)) ∨ IsSquare (φ (wordOver ℤ K L)) ∨
      IsSquare (φ (wordOver ℤ I J) * φ (wordOver ℤ K L)) := by
  have h₃ := congrArg φ (word_overlap ℤ I J K L).symm
  have hh := congrArg φ (word_remove_overlap ℤ I J K L)
  simp only [map_mul, map_pow] at h₃ hh
  have hne : φ (A 0) ≠ 0 ∨ φ (A 1) ≠ 0 ∨ φ (A 2) ≠ 0 ∨ φ (A 3) ≠ 0 := by
    obtain ⟨χ, hχ⟩ := hA
    fin_cases χ <;> tauto
  rw [normPolynomial, map_sourceNorm] at hR
  exact source_dependence _ _ _ _ _ _ _ _ _ (overlap_ne_zero φ I J K L h₁ h₂) h₃
    (by simpa only [mul_comm] using hh) hne hR

theorem primitive_survives {F : Type*} [Field F] (φ : ℤ[X][X] →+* F)
    (C : ℤ[X][X]) (hC : ¬ IsUnit C) (hker : ∀ P, φ P = 0 ↔ C ∣ P)
    (A : Fin 4 → ℤ[X][X]) (hprimitive : ∀ E : ℤ[X][X], (∀ χ, E ∣ A χ) → IsUnit E) :
    ∃ χ, φ (A χ) ≠ 0 := by
  by_contra hn
  push Not at hn
  exact hC (hprimitive C (fun χ ↦ (hker (A χ)).mp (hn χ)))

theorem dependent_on_curve {F : Type*} [Field F] [CharZero F] (φ : ℤ[X][X] →+* F)
    (C : ℤ[X][X]) (hC : ¬ IsUnit C) (hker : ∀ P, φ P = 0 ↔ C ∣ P)
    (I J K L : Finset ℤ) (A : Fin 4 → ℤ[X][X])
    (hprimitive : ∀ E : ℤ[X][X], (∀ χ, E ∣ A χ) → IsUnit E)
    (h₁ : φ (wordOver ℤ I J) ≠ 0) (h₂ : φ (wordOver ℤ K L) ≠ 0)
    (hdiv : C ∣ normPolynomial I J K L A) :
    IsSquare (φ (wordOver ℤ I J)) ∨ IsSquare (φ (wordOver ℤ K L)) ∨
      IsSquare (φ (wordOver ℤ I J) * φ (wordOver ℤ K L)) :=
  word_dependence φ I J K L A h₁ h₂ (primitive_survives φ C hC hker A hprimitive)
    ((hker _).mpr hdiv)

end PaperP1.CurveNormCollapse
