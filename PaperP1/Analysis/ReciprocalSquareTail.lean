module

public import PaperP1.Arithmetic.CoprimeIntervalPairs
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Analysis.Real.Sqrt

/-! # Explicit finite reciprocal-square tails, with an arbitrary real lower endpoint -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ReciprocalSquareTail

open Finset

theorem interval_bound (D M : ℕ) (hD : 0 < D) :
    (∑ d ∈ Icc D M, 1 / (d : ℝ) ^ 2) ≤ 2 / (D : ℝ) := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hstep (m : ℝ) (hm : 0 < m) :
      1 / (m + 1) ^ 2 ≤ 1 / m - 1 / (m + 1) := by
    calc
      _ ≤ 1 / (m * (m + 1)) := one_div_le_one_div_of_le (by positivity) (by nlinarith only [hm])
      _ = _ := by field_simp; ring
  have hstrong (k : ℕ) : (∑ d ∈ Icc D (D + k), 1 / (d : ℝ) ^ 2) ≤
      1 / (D : ℝ) ^ 2 + 1 / D - 1 / ((D + k : ℕ) : ℝ) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show D + (k + 1) = (D + k) + 1 by omega, sum_Icc_succ_top (by omega)]
      have hh := add_le_add ih (hstep ((D + k : ℕ) : ℝ) (by exact_mod_cast (show 0 < D + k by omega)))
      push_cast at hh ⊢
      linarith only [hh]
  by_cases hDM : D ≤ M
  · have hh := hstrong (M - D)
    rw [Nat.add_sub_of_le hDM] at hh
    have hone : (1 : ℝ) ≤ D := by exact_mod_cast hD
    have hsq : 1 / (D : ℝ) ^ 2 ≤ 1 / D :=
      one_div_le_one_div_of_le hDr (by nlinarith only [hone])
    have hlast : (0 : ℝ) ≤ 1 / M := by positivity
    calc
      _ ≤ 1 / (D : ℝ) ^ 2 + 1 / D := hh.trans (sub_le_self _ hlast)
      _ ≤ 1 / (D : ℝ) + 1 / D := add_le_add hsq (le_refl _)
      _ = _ := by ring
  · rw [Icc_eq_empty (by omega), sum_empty]
    positivity

theorem finite_bound (A : ℝ) (hA : 0 < A) (S : Finset ℕ)
    (hS : ∀ d ∈ S, A ≤ d) :
    (∑ d ∈ S, 1 / (d : ℝ) ^ 2) ≤ 2 / A := by
  classical
  have hD : 0 < ⌈A⌉₊ := Nat.ceil_pos.mpr hA
  have hsub : S ⊆ Icc ⌈A⌉₊ (S.sup id) := by
    intro d hd
    exact mem_Icc.mpr ⟨Nat.ceil_le.mpr (hS d hd), le_sup (f := id) hd⟩
  calc
    _ ≤ ∑ d ∈ Icc ⌈A⌉₊ (S.sup id), 1 / (d : ℝ) ^ 2 :=
      sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
    _ ≤ 2 / (⌈A⌉₊ : ℝ) := interval_bound _ _ hD
    _ ≤ 2 / A := div_le_div_of_nonneg_left (by norm_num) hA (Nat.le_ceil A)

theorem product_bound (A B : ℝ) (hA : 0 < A) (hB : 0 < B)
    (R : Finset (ℕ × ℕ)) (hR : ∀ z ∈ R, A ≤ z.1 ∧ B ≤ z.2) :
    (∑ z ∈ R, 1 / ((z.1 : ℝ) ^ 2 * (z.2 : ℝ) ^ 2)) ≤ 4 / (A * B) := by
  classical
  have hsub : R ⊆ (R.image Prod.fst) ×ˢ (R.image Prod.snd) := by
    intro z hz
    exact mem_product.mpr ⟨mem_image_of_mem _ hz, mem_image_of_mem _ hz⟩
  have hfst := finite_bound A hA (R.image Prod.fst) (by
    intro d hd; obtain ⟨z, hz, rfl⟩ := mem_image.mp hd; exact (hR z hz).1)
  have hsnd := finite_bound B hB (R.image Prod.snd) (by
    intro d hd; obtain ⟨z, hz, rfl⟩ := mem_image.mp hd; exact (hR z hz).2)
  calc
    _ ≤ ∑ z ∈ (R.image Prod.fst) ×ˢ (R.image Prod.snd), 1 / ((z.1 : ℝ) ^ 2 * (z.2 : ℝ) ^ 2) :=
      sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
    _ = (∑ d ∈ R.image Prod.fst, 1 / (d : ℝ) ^ 2) * (∑ e ∈ R.image Prod.snd, 1 / (e : ℝ) ^ 2) := by
      rw [sum_product, sum_mul_sum]
      simp only [one_div_mul_one_div]
    _ ≤ (2 / A) * (2 / B) := mul_le_mul hfst hsnd (by positivity) (by positivity)
    _ = _ := by ring

theorem weighted_product_bound (c₁ c₂ R : ℝ) (hc₁ : 1 ≤ c₁) (hc₂ : 1 ≤ c₂)
    (hR : 0 < R) (S : Finset (ℕ × ℕ))
    (hS : ∀ z ∈ S, R ≤ c₁ * (z.1 : ℝ) ^ 2 ∧ R ≤ c₂ * (z.2 : ℝ) ^ 2) :
    (∑ z ∈ S, 1 / (c₁ * c₂ * (z.1 : ℝ) ^ 2 * (z.2 : ℝ) ^ 2)) ≤ 4 / R := by
  have hc₁pos : 0 < c₁ := by linarith only [hc₁]
  have hc₂pos : 0 < c₂ := by linarith only [hc₂]
  let A := Real.sqrt (R / c₁)
  let B := Real.sqrt (R / c₂)
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hdata : ∀ z ∈ S, A ≤ z.1 ∧ B ≤ z.2 := by
    intro z hz
    exact ⟨(Real.sqrt_le_left (Nat.cast_nonneg z.1)).mpr ((div_le_iff₀ hc₁pos).mpr (by nlinarith only [(hS z hz).1])),
      (Real.sqrt_le_left (Nat.cast_nonneg z.2)).mpr ((div_le_iff₀ hc₂pos).mpr (by nlinarith only [(hS z hz).2]))⟩
  have hscale (c : ℝ) (hc : 1 ≤ c) : Real.sqrt R ≤ c * Real.sqrt (R / c) := by
    have hcpos : 0 < c := by linarith only [hc]
    have hsq := Real.sq_sqrt (div_nonneg hR.le hcpos.le)
    have hprod : R ≤ (c * Real.sqrt (R / c)) ^ 2 := by
      have hid : (c * Real.sqrt (R / c)) ^ 2 = c * R := by
        rw [mul_pow, hsq]
        field_simp
      rw [hid]
      nlinarith only [hc, hR.le]
    exact (Real.sqrt_le_left (by positivity)).mpr hprod
  have hden : R ≤ c₁ * c₂ * (A * B) := by
    have hh := mul_le_mul (hscale c₁ hc₁) (hscale c₂ hc₂) (Real.sqrt_nonneg R) (by positivity)
    rw [Real.mul_self_sqrt hR.le] at hh
    nlinarith only [hh]
  calc
    _ = (1 / (c₁ * c₂)) * ∑ z ∈ S, 1 / ((z.1 : ℝ) ^ 2 * (z.2 : ℝ) ^ 2) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro z _
      ring
    _ ≤ (1 / (c₁ * c₂)) * (4 / (A * B)) :=
      mul_le_mul_of_nonneg_left (product_bound A B hA hB S hdata) (by positivity)
    _ = 4 / (c₁ * c₂ * (A * B)) := by ring
    _ ≤ 4 / R := div_le_div_of_nonneg_left (by norm_num) hR hden

end PaperP1.ReciprocalSquareTail
