module

public import PaperP1.Analysis.BiquadraticWordValues

/-! # At the actual square point the enumerated four-term auxiliary is an integer -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BiquadraticWordRealization

open Finset Polynomial PaperP1.BiquadraticWordEnumeration PaperP1.BiquadraticWordValues
  PaperP1.BiquadraticWordNorm PaperP1.FormalWordPolynomials PaperP1.BiquadraticAuxiliaryValue
open scoped symmDiff

theorem auxiliary_realization (I J K L : Finset ℤ) (r s : Fin 3 → ℕ)
    (hcx : I.card = 2 * r 0 ∧ K.card = 2 * r 1 ∧ (I ∆ K).card = 2 * r 2)
    (hcy : J.card = 2 * s 0 ∧ L.card = 2 * s 1 ∧ (J ∆ L).card = 2 * s 2)
    (A : Fin 4 → ℤ[X][X]) (B : ℕ) (hB : 1 ≤ B) (x y : ℤ)
    (hx : 4 * (B : ℤ) ≤ x) (hy : 4 * (B : ℤ) ≤ y)
    (hI : ∀ i ∈ I, |i| ≤ (B : ℤ)) (hJ : ∀ j ∈ J, |j| ≤ (B : ℤ))
    (hK : ∀ i ∈ K, |i| ≤ (B : ℤ)) (hL : ∀ j ∈ L, |j| ≤ (B : ℤ))
    (h₁ : IsSquare ((wordOver ℤ I J).evalEval x y)) (h₂ : IsSquare ((wordOver ℤ K L).evalEval x y)) :
    ∃ w₁ w₂ w₃ : ℤ, 0 < w₁ ∧ 0 < w₂ ∧ 0 < w₃ ∧
      w₁ ^ 2 = (wordOver ℤ I J).evalEval x y ∧ w₂ ^ 2 = (wordOver ℤ K L).evalEval x y ∧
      w₃ ^ 2 = (wordOver ℤ (I ∆ K) (J ∆ L)).evalEval x y ∧
      (wordOver ℤ (I ∩ K) (J ∩ L)).evalEval x y * w₃ = w₁ * w₂ ∧
      auxiliaryValue A (rootLists I K r hcx) (rootLists J L s hcy) (x : ℝ) (y : ℝ) =
        ((((A 0).evalEval x y + (A 1).evalEval x y * w₁ + (A 2).evalEval x y * w₂ +
          (A 3).evalEval x y * w₃ : ℤ)) : ℝ) := by
  let γ := rootLists I K r hcx
  let δ := rootLists J L s hcy
  have hxpos : 0 < x := by omega
  have hypos : 0 < y := by omega
  have hxR : (0 : ℝ) < x := by exact_mod_cast hxpos
  have hyR : (0 : ℝ) < y := by exact_mod_cast hypos
  have hγ : ∀ χ i, |(γ χ i : ℝ) * (1 / (x : ℝ))| ≤ 1 / 4 := by
    intro χ i
    exact RungeSeriesValues.small_parameter (γ χ i) B (x : ℝ) hxR (by exact_mod_cast hx)
      (rootLists_bound I K r hcx B hI hK χ i)
  have hδ : ∀ χ i, |(δ χ i : ℝ) * (1 / (y : ℝ))| ≤ 1 / 4 := by
    intro χ i
    exact RungeSeriesValues.small_parameter (δ χ i) B (y : ℝ) hyR (by exact_mod_cast hy)
      (rootLists_bound J L s hcy B hJ hL χ i)
  obtain ⟨w₁, w₂, w₃, hw₁, hw₂, hw₃, hs₁, hs₂, hs₃, hprod⟩ :=
    square_point_roots I J K L B x y (by omega) (by omega) hI hJ hK hL h₁ h₂
  let W : Fin 4 → ℤ := ![1, w₁, w₂, w₃]
  have hWpos : ∀ χ, 0 < W χ := by
    intro χ
    fin_cases χ
    · norm_num [W]
    · exact hw₁
    · exact hw₂
    · exact hw₃
  have hWsq : ∀ χ, (W χ) ^ 2 = (wordOver ℤ (offsets I K χ) (offsets J L χ)).evalEval x y := by
    intro χ
    fin_cases χ
    · simp [W, offsets, wordOver, linearOver]
    · exact hs₁
    · exact hs₂
    · exact hs₃
  have hroot : ∀ χ, rootValue γ δ χ (x : ℝ) (y : ℝ) = (W χ : ℝ) := by
    intro χ
    exact enumerated_integer I J K L r s hcx hcy χ x y (W χ) hxpos hypos (hWpos χ) (hWsq χ) (hγ χ) (hδ χ)
  have heq : auxiliaryValue A γ δ (x : ℝ) (y : ℝ) =
      (((∑ χ : Fin 4, (A χ).evalEval x y * W χ : ℤ)) : ℝ) := by
    unfold auxiliaryValue
    push_cast
    apply sum_congr rfl
    intro χ _
    rw [BivariateEvaluation.integer_evaluation]
    change (((A χ).evalEval x y : ℤ) : ℝ) * rootValue γ δ χ (x : ℝ) (y : ℝ) =
      (((A χ).evalEval x y : ℤ) : ℝ) * (W χ : ℝ)
    rw [hroot χ]
  have hsum : (∑ χ : Fin 4, (A χ).evalEval x y * W χ) =
      (A 0).evalEval x y + (A 1).evalEval x y * w₁ + (A 2).evalEval x y * w₂ + (A 3).evalEval x y * w₃ := by
    simp [Fin.sum_univ_succ, W, add_assoc]
  refine ⟨w₁, w₂, w₃, hw₁, hw₂, hw₃, hs₁, hs₂, hs₃, hprod, ?_⟩
  rw [heq, hsum]

theorem integer_value (I J K L : Finset ℤ) (r s : Fin 3 → ℕ)
    (hcx : I.card = 2 * r 0 ∧ K.card = 2 * r 1 ∧ (I ∆ K).card = 2 * r 2)
    (hcy : J.card = 2 * s 0 ∧ L.card = 2 * s 1 ∧ (J ∆ L).card = 2 * s 2)
    (A : Fin 4 → ℤ[X][X]) (B : ℕ) (hB : 1 ≤ B) (x y : ℤ)
    (hx : 4 * (B : ℤ) ≤ x) (hy : 4 * (B : ℤ) ≤ y)
    (hI : ∀ i ∈ I, |i| ≤ (B : ℤ)) (hJ : ∀ j ∈ J, |j| ≤ (B : ℤ))
    (hK : ∀ i ∈ K, |i| ≤ (B : ℤ)) (hL : ∀ j ∈ L, |j| ≤ (B : ℤ))
    (h₁ : IsSquare ((wordOver ℤ I J).evalEval x y)) (h₂ : IsSquare ((wordOver ℤ K L).evalEval x y)) :
    ∃ z : ℤ, auxiliaryValue A (rootLists I K r hcx) (rootLists J L s hcy) (x : ℝ) (y : ℝ) = (z : ℝ) := by
  obtain ⟨w₁, w₂, w₃, _hw₁, _hw₂, _hw₃, _hs₁, _hs₂, _hs₃, _hprod, heq⟩ :=
    auxiliary_realization I J K L r s hcx hcy A B hB x y hx hy hI hJ hK hL h₁ h₂
  exact ⟨_, heq⟩

theorem norm_point_zero (I J K L : Finset ℤ) (r s : Fin 3 → ℕ)
    (hcx : I.card = 2 * r 0 ∧ K.card = 2 * r 1 ∧ (I ∆ K).card = 2 * r 2)
    (hcy : J.card = 2 * s 0 ∧ L.card = 2 * s 1 ∧ (J ∆ L).card = 2 * s 2)
    (A : Fin 4 → ℤ[X][X]) (B : ℕ) (hB : 1 ≤ B) (x y : ℤ)
    (hx : 4 * (B : ℤ) ≤ x) (hy : 4 * (B : ℤ) ≤ y)
    (hI : ∀ i ∈ I, |i| ≤ (B : ℤ)) (hJ : ∀ j ∈ J, |j| ≤ (B : ℤ))
    (hK : ∀ i ∈ K, |i| ≤ (B : ℤ)) (hL : ∀ j ∈ L, |j| ≤ (B : ℤ))
    (h₁ : IsSquare ((wordOver ℤ I J).evalEval x y)) (h₂ : IsSquare ((wordOver ℤ K L).evalEval x y))
    (haux : auxiliaryValue A (rootLists I K r hcx) (rootLists J L s hcy) (x : ℝ) (y : ℝ) = 0) :
    (normPolynomial I J K L A).evalEval x y = 0 := by
  obtain ⟨w₁, w₂, w₃, _hw₁, _hw₂, _hw₃, hs₁, hs₂, hs₃, hprod, heq⟩ :=
    auxiliary_realization I J K L r s hcx hcy A B hB x y hx hy hI hJ hK hL h₁ h₂
  have hzero : (A 0).evalEval x y + (A 1).evalEval x y * w₁ + (A 2).evalEval x y * w₂ +
      (A 3).evalEval x y * w₃ = 0 := by
    have hh := heq.symm.trans haux
    exact_mod_cast hh
  have hG : (wordOver ℤ (I ∩ K) (J ∩ L)).evalEval x y ≠ 0 :=
    (word_value_pos_of_bounds _ _ B x y (by omega) (by omega)
      (fun i hi ↦ hI i (mem_inter.mp hi).1) (fun j hj ↦ hJ j (mem_inter.mp hj).1)).ne'
  exact normPolynomial_evaluate_zero I J K L A x y w₁ w₂ w₃ hG hs₁ hs₂ hs₃ hprod hzero

end PaperP1.BiquadraticWordRealization
