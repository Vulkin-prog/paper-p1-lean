module

public import PaperP1.Analysis.BiquadraticAuxiliaryValue
public import PaperP1.Arithmetic.BiquadraticWordEnumeration

/-! # Enumerated formal branches realize the actual positive integer word roots -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BiquadraticWordValues

open Finset Polynomial PaperP1.BiquadraticRungeMatrix PaperP1.BiquadraticFormalNumerator
  PaperP1.BiquadraticWordEnumeration PaperP1.BivariateSeriesValue PaperP1.RungePowerSeries
  PaperP1.FormalWordPolynomials PaperP1.BiquadraticWordNorm
open scoped symmDiff

def rootValue {r s : Fin 3 → ℕ}
    (γ : (χ : Fin 4) → Fin (2 * blockRank r χ) → ℤ)
    (δ : (χ : Fin 4) → Fin (2 * blockRank s χ) → ℤ) (χ : Fin 4) (x y : ℝ) : ℝ :=
  x ^ blockRank r χ * y ^ blockRank s χ * value (branch (γ χ) (δ χ)) (1 / x) (1 / y)

theorem rootValue_product {r s : Fin 3 → ℕ}
    (γ : (χ : Fin 4) → Fin (2 * blockRank r χ) → ℤ)
    (δ : (χ : Fin 4) → Fin (2 * blockRank s χ) → ℤ) (χ : Fin 4) (x y : ℝ)
    (hγ : ∀ i, |(γ χ i : ℝ) * (1 / x)| < 1) (hδ : ∀ i, |(δ χ i : ℝ) * (1 / y)| < 1) :
    rootValue γ δ χ x y =
      (x ^ blockRank r χ * RealSeriesEvaluation.value (rungeProductSeries (γ χ)) (1 / x)) *
        (y ^ blockRank s χ * RealSeriesEvaluation.value (rungeProductSeries (δ χ)) (1 / y)) := by
  rw [rootValue, value_branch _ _ _ _ hγ hδ]
  ring

theorem rootValue_positive {r s : Fin 3 → ℕ}
    (γ : (χ : Fin 4) → Fin (2 * blockRank r χ) → ℤ)
    (δ : (χ : Fin 4) → Fin (2 * blockRank s χ) → ℤ) (χ : Fin 4) (x y : ℝ)
    (hx : 0 < x) (hy : 0 < y)
    (hγ : ∀ i, |(γ χ i : ℝ) * (1 / x)| ≤ 1 / 4) (hδ : ∀ i, |(δ χ i : ℝ) * (1 / y)| ≤ 1 / 4) :
    0 < rootValue γ δ χ x y := by
  rw [rootValue_product γ δ χ x y (fun i ↦ by have h := hγ i; linarith) (fun i ↦ by have h := hδ i; linarith)]
  exact mul_pos (RungeSeriesValues.scaled_product_positive (γ χ) x hx hγ)
    (RungeSeriesValues.scaled_product_positive (δ χ) y hy hδ)

theorem enumerated_square (I J K L : Finset ℤ) (r s : Fin 3 → ℕ)
    (hcx : I.card = 2 * r 0 ∧ K.card = 2 * r 1 ∧ (I ∆ K).card = 2 * r 2)
    (hcy : J.card = 2 * s 0 ∧ L.card = 2 * s 1 ∧ (J ∆ L).card = 2 * s 2)
    (χ : Fin 4) (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0)
    (hγ : ∀ i, |(rootLists I K r hcx χ i : ℝ) * (1 / (x : ℝ))| < 1)
    (hδ : ∀ i, |(rootLists J L s hcy χ i : ℝ) * (1 / (y : ℝ))| < 1) :
    rootValue (rootLists I K r hcx) (rootLists J L s hcy) χ (x : ℝ) (y : ℝ) ^ 2 =
      (((wordOver ℤ (offsets I K χ) (offsets J L χ)).evalEval x y : ℤ) : ℝ) := by
  have hxR : (x : ℝ) ≠ 0 := by exact_mod_cast hx
  have hyR : (y : ℝ) ≠ 0 := by exact_mod_cast hy
  rw [rootValue_product _ _ χ (x : ℝ) (y : ℝ) hγ hδ, mul_pow,
    RungeSeriesValues.scaled_product_square _ _ hxR hγ, RungeSeriesValues.scaled_product_square _ _ hyR hδ,
    rootLists_product I K r hcx χ (fun u : ℤ ↦ (x : ℝ) + (u : ℝ)),
    rootLists_product J L s hcy χ (fun u : ℤ ↦ (y : ℝ) + (u : ℝ)), word_evaluation]
  push_cast
  rfl

theorem enumerated_integer (I J K L : Finset ℤ) (r s : Fin 3 → ℕ)
    (hcx : I.card = 2 * r 0 ∧ K.card = 2 * r 1 ∧ (I ∆ K).card = 2 * r 2)
    (hcy : J.card = 2 * s 0 ∧ L.card = 2 * s 1 ∧ (J ∆ L).card = 2 * s 2)
    (χ : Fin 4) (x y w : ℤ) (hx : 0 < x) (hy : 0 < y) (hw : 0 < w)
    (hsq : w ^ 2 = (wordOver ℤ (offsets I K χ) (offsets J L χ)).evalEval x y)
    (hγ : ∀ i, |(rootLists I K r hcx χ i : ℝ) * (1 / (x : ℝ))| ≤ 1 / 4)
    (hδ : ∀ i, |(rootLists J L s hcy χ i : ℝ) * (1 / (y : ℝ))| ≤ 1 / 4) :
    rootValue (rootLists I K r hcx) (rootLists J L s hcy) χ (x : ℝ) (y : ℝ) = (w : ℝ) := by
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hyR : (0 : ℝ) < y := by exact_mod_cast hy
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  have hpos := rootValue_positive _ _ χ (x : ℝ) (y : ℝ) hxR hyR hγ hδ
  have hfirst := enumerated_square I J K L r s hcx hcy χ x y hx.ne' hy.ne'
    (fun i ↦ by have h := hγ i; linarith) (fun i ↦ by have h := hδ i; linarith)
  have hsecond : (w : ℝ) ^ 2 = (((wordOver ℤ (offsets I K χ) (offsets J L χ)).evalEval x y : ℤ) : ℝ) := by
    exact_mod_cast hsq
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hfirst.trans hsecond.symm) with h | h
  · exact h
  · linarith

theorem positive_integer_root (f : ℤ) (hf : 0 < f) (hsq : IsSquare f) : ∃ w : ℤ, 0 < w ∧ w ^ 2 = f := by
  obtain ⟨u, hu⟩ := hsq.exists_sq
  have hune : u ≠ 0 := by intro h; rw [h, zero_pow (by decide : 2 ≠ 0)] at hu; linarith
  refine ⟨|u|, abs_pos.mpr hune, ?_⟩
  simpa only [sq_abs] using hu.symm

theorem square_point_roots (I J K L : Finset ℤ) (B : ℕ) (x y : ℤ)
    (hx : (B : ℤ) < x) (hy : (B : ℤ) < y)
    (hI : ∀ i ∈ I, |i| ≤ (B : ℤ)) (hJ : ∀ j ∈ J, |j| ≤ (B : ℤ))
    (hK : ∀ i ∈ K, |i| ≤ (B : ℤ)) (hL : ∀ j ∈ L, |j| ≤ (B : ℤ))
    (h₁ : IsSquare ((wordOver ℤ I J).evalEval x y)) (h₂ : IsSquare ((wordOver ℤ K L).evalEval x y)) :
    ∃ w₁ w₂ w₃ : ℤ, 0 < w₁ ∧ 0 < w₂ ∧ 0 < w₃ ∧
      w₁ ^ 2 = (wordOver ℤ I J).evalEval x y ∧ w₂ ^ 2 = (wordOver ℤ K L).evalEval x y ∧
      w₃ ^ 2 = (wordOver ℤ (I ∆ K) (J ∆ L)).evalEval x y ∧
      (wordOver ℤ (I ∩ K) (J ∩ L)).evalEval x y * w₃ = w₁ * w₂ := by
  obtain ⟨w₁, hw₁, hs₁⟩ := positive_integer_root _ (word_value_pos_of_bounds I J B x y hx hy hI hJ) h₁
  obtain ⟨w₂, hw₂, hs₂⟩ := positive_integer_root _ (word_value_pos_of_bounds K L B x y hx hy hK hL) h₂
  have hG : 0 < (wordOver ℤ (I ∩ K) (J ∩ L)).evalEval x y :=
    word_value_pos_of_bounds _ _ B x y hx hy (fun i hi ↦ hI i (mem_inter.mp hi).1)
      (fun j hj ↦ hJ j (mem_inter.mp hj).1)
  obtain ⟨w₃, hs₃, hprod⟩ := exists_third_root I J K L x y w₁ w₂ hG.ne' hs₁ hs₂
  have hw₃ : 0 < w₃ := by
    apply (mul_pos_iff_of_pos_left hG).mp
    rw [hprod]
    exact mul_pos hw₁ hw₂
  exact ⟨w₁, w₂, w₃, hw₁, hw₂, hw₃, hs₁, hs₂, hs₃, hprod⟩

end PaperP1.BiquadraticWordValues
