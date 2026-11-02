module

public import PaperP1.Analysis.BiquadraticAuxiliaryGap
public import PaperP1.Analysis.BiquadraticWordRealization
public import PaperP1.Arithmetic.BiquadraticAlgebraicAuxiliary

/-! # The actual square point lies on a nonzero bounded integer polynomial -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoWitnessPolynomial

open Finset Polynomial PaperP1.BivariateDegrees PaperP1.BivariateTotalDegree
  PaperP1.FormalWordPolynomials PaperP1.BiquadraticWordNorm PaperP1.BiquadraticWordEnumeration
  PaperP1.BiquadraticAuxiliaryValue
open scoped symmDiff

theorem threshold (B q : ℕ) (hq : 1 ≤ q) (hqB : q ≤ B) (N : ℝ)
    (hlarge : ((B : ℝ) + 1) ^ (1200 * q) < N) :
    8 * (B : ℝ) ≤ N ∧ ((B : ℝ) + 1) ^ (400 * q) < N := by
  have hbase : 2 ≤ B + 1 := by omega
  have hfour : 4 * B ≤ (B + 1) ^ 2 := by
    have hz : 4 * (B : ℤ) ≤ ((B : ℤ) + 1) ^ 2 := by nlinarith [sq_nonneg ((B : ℤ) - 1)]
    exact_mod_cast hz
  have height : 8 * B ≤ (B + 1) ^ 3 := by
    calc
      _ = 2 * (4 * B) := by ring
      _ ≤ (B + 1) * (B + 1) ^ 2 := Nat.mul_le_mul hbase hfour
      _ = _ := by ring
  have hfull : 8 * B ≤ (B + 1) ^ (1200 * q) :=
    height.trans (Nat.pow_le_pow_right (by omega) (by omega))
  have hfullR : 8 * (B : ℝ) ≤ ((B : ℝ) + 1) ^ (1200 * q) := by exact_mod_cast hfull
  have hbaseR : (1 : ℝ) ≤ (B : ℝ) + 1 := by have h := Nat.cast_nonneg (α := ℝ) B; linarith
  exact ⟨hfullR.trans hlarge.le, (pow_le_pow_right₀ hbaseR (by omega : 400 * q ≤ 1200 * q)).trans_lt hlarge⟩

theorem exists_polynomial {q : ℕ} {r s : Fin 3 → ℕ} (B : ℕ) (hq : 1 ≤ q) (hqB : q ≤ B)
    (hr : ∀ i, r i ≤ q) (hs : ∀ i, s i ≤ q)
    (I J K L : Finset ℤ) (hind : Independent I J K L)
    (hI : ∀ i ∈ I, |i| ≤ (B : ℤ)) (hJ : ∀ j ∈ J, |j| ≤ (B : ℤ))
    (hK : ∀ i ∈ K, |i| ≤ (B : ℤ)) (hL : ∀ j ∈ L, |j| ≤ (B : ℤ))
    (hcx : I.card = 2 * r 0 ∧ K.card = 2 * r 1 ∧ (I ∆ K).card = 2 * r 2)
    (hcy : J.card = 2 * s 0 ∧ L.card = 2 * s 1 ∧ (J ∆ L).card = 2 * s 2)
    (N : ℝ) (x y : ℤ) (hx : N ≤ (x : ℝ)) (hy : N ≤ (y : ℝ))
    (hx₂ : (x : ℝ) ≤ 2 * N) (hy₂ : (y : ℝ) ≤ 2 * N)
    (hlarge : ((B : ℝ) + 1) ^ (1200 * q) < N)
    (h₁ : IsSquare ((wordOver ℤ I J).evalEval x y)) (h₂ : IsSquare ((wordOver ℤ K L).evalEval x y)) :
    ∃ Q : Fin 4 → ℤ[X][X], ∃ R : ℤ[X][X],
      (∀ E : ℤ[X][X], (∀ χ, E ∣ Q χ) → IsUnit E) ∧ (∃ χ, Q χ ≠ 0) ∧
      (∀ χ, BivariateHeight.height (Q χ) ≤ (B + 1) ^ (275 * q)) ∧
      R = normPolynomial I J K L Q ∧ R ≠ 0 ∧ R.evalEval x y = 0 ∧
      degreeX R ≤ 12 * q ∧ degreeY R ≤ 12 * q ∧ totalDegree R ≤ 24 * q ∧
      BivariateHeight.height R ≤ (B + 1) ^ (1200 * q) := by
  let γ := rootLists I K r hcx
  let δ := rootLists J L s hcy
  have hγ := rootLists_bound I K r hcx B hI hK
  have hδ := rootLists_bound J L s hcy B hJ hL
  obtain ⟨w, D, Q, R, hD, hfactor, hprimitive, hQ, hDdeg, hQdeg, hQheight, hR, hRne,
      hRdeg, hRheight, _hprod, hzero, _hdiv⟩ :=
    BiquadraticAlgebraicAuxiliary.exists_auxiliary B hq hqB hr hs I J K L hind hI hJ hK hL hcx hcy γ δ hγ hδ
  obtain ⟨hN, hNlarge⟩ := threshold B q hq hqB N hlarge
  have hbound := BiquadraticAuxiliaryGap.primitive_bound B hq hqB hr hs w D Q hD hfactor hDdeg hQdeg hQheight
    γ δ hγ hδ hzero N (x : ℝ) (y : ℝ) hN hx hy hx₂ hy₂
  have hB : 1 ≤ B := hq.trans hqB
  have hB₀ : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hx₄ : 4 * (B : ℤ) ≤ x := by
    have hh : 4 * (B : ℝ) ≤ (x : ℝ) := by linarith
    exact_mod_cast hh
  have hy₄ : 4 * (B : ℤ) ≤ y := by
    have hh : 4 * (B : ℝ) ≤ (y : ℝ) := by linarith
    exact_mod_cast hh
  obtain ⟨z, hz⟩ := BiquadraticWordRealization.integer_value I J K L r s hcx hcy Q B hB x y hx₄ hy₄ hI hJ hK hL h₁ h₂
  have hNp : 0 < N := (by positivity : 0 < ((B : ℝ) + 1) ^ (1200 * q)).trans hlarge
  have haux := BiquadraticAuxiliaryGap.integer_gap (auxiliaryValue Q γ δ (x : ℝ) (y : ℝ)) N
    (((B : ℝ) + 1) ^ (400 * q)) z hz hNp hNlarge hbound
  have hpoint := BiquadraticWordRealization.norm_point_zero I J K L r s hcx hcy Q B hB x y hx₄ hy₄ hI hJ hK hL h₁ h₂ haux
  refine ⟨Q, R, hprimitive, hQ, hQheight, hR, hRne, ?_, hRdeg.1, hRdeg.2.1, hRdeg.2.2, hRheight⟩
  rwa [hR]

end PaperP1.TwoWitnessPolynomial
