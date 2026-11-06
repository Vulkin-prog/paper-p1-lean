module

public import PaperP1.Analysis.FiniteSymmetricKernelBudget
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Topology.Algebra.InfiniteSum.Order

/-! # Explicit Gaussian frequency-row bounds from natural-index and logarithmic separation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GaussianFrequencyRowBound
open Finset MeasureTheory
open scoped Classical

theorem gaussian_antitone (c : ℝ) (hc : 0 ≤ c) :
    AntitoneOn (fun x : ℝ ↦ Real.exp (-c*x^2)) (Set.Ici 0) := by
  intro x hx y hy hxy
  apply Real.exp_le_exp.mpr
  have hsq : x^2 ≤ y^2 := by nlinarith [show 0 ≤ x from hx, show 0 ≤ y from hy]
  nlinarith

theorem gaussian_tail_summable (c : ℝ) (hc : 0 < c) :
    Summable (fun n : ℕ ↦ Real.exp (-c*((n+1 : ℕ) : ℝ)^2)) := by
  have ha := gaussian_antitone c hc.le
  have hs := ha.summable_of_integrableOn_Ioi_zero
    (integrable_exp_neg_mul_sq hc).integrableOn (fun _ _ ↦ (Real.exp_pos _).le)
  exact (summable_nat_add_iff 1).mpr hs

theorem gaussian_tail_bound (c : ℝ) (hc : 0 < c) :
    (∑' n : ℕ, Real.exp (-c*((n+1 : ℕ) : ℝ)^2)) ≤ Real.sqrt (Real.pi/c) / 2 := by
  have ha := gaussian_antitone c hc.le
  have hh := ha.tsum_add_one_le_integral
    (integrable_exp_neg_mul_sq hc).integrableOn (fun _ _ ↦ (Real.exp_pos _).le)
  simpa only [integral_gaussian_Ioi] using hh

theorem translated_sequence_bound (S : Finset ℕ) (i : ℕ) (h g : ℕ → ℝ)
    (hg : Summable g) (hg0 : ∀ n, 0 ≤ g n) (hcenter : h i ≤ 1)
    (hleft : ∀ j ∈ S, j < i → h j ≤ g (i-j-1))
    (hright : ∀ j ∈ S, i < j → h j ≤ g (j-i-1)) :
    (∑ j ∈ S, h j) ≤ 1 + 2 * ∑' n : ℕ, g n := by
  have hL : (∑ j ∈ S.filter (fun j ↦ j < i), g (i-j-1)) ≤ ∑' n, g n := by
    have hinj : Set.InjOn (fun j : ℕ ↦ i-j-1) (S.filter (fun j ↦ j < i)) := by
      intro j hj k hk he
      change i-j-1 = i-k-1 at he
      have hj' := (mem_filter.mp hj).2
      have hk' := (mem_filter.mp hk).2
      omega
    have hh := hg.sum_le_tsum ((S.filter (fun j ↦ j < i)).image (fun j ↦ i-j-1)) (fun _ _ ↦ hg0 _)
    rw [sum_image hinj] at hh
    exact hh
  have hR : (∑ j ∈ S.filter (fun j ↦ i < j), g (j-i-1)) ≤ ∑' n, g n := by
    have hinj : Set.InjOn (fun j : ℕ ↦ j-i-1) (S.filter (fun j ↦ i < j)) := by
      intro j hj k hk he
      change j-i-1 = k-i-1 at he
      have hj' := (mem_filter.mp hj).2
      have hk' := (mem_filter.mp hk).2
      omega
    have hh := hg.sum_le_tsum ((S.filter (fun j ↦ i < j)).image (fun j ↦ j-i-1)) (fun _ _ ↦ hg0 _)
    rw [sum_image hinj] at hh
    exact hh
  have hpoint : (∑ j ∈ S, h j) ≤
      (∑ j ∈ S, if j = i then (1 : ℝ) else 0) +
      (∑ j ∈ S, if j < i then g (i-j-1) else 0) +
      (∑ j ∈ S, if i < j then g (j-i-1) else 0) := by
    rw [← sum_add_distrib, ← sum_add_distrib]
    apply sum_le_sum
    intro j hj
    by_cases hji : j = i
    · subst j
      simp only [lt_self_iff_false, ite_false, ite_true, add_zero]
      exact hcenter
    · rcases lt_or_gt_of_ne hji with hjl | hjr
      · simpa only [hji, hjl, not_lt_of_ge hjl.le, ite_true, ite_false, zero_add, add_zero] using hleft j hj hjl
      · simpa only [hji, hjr, not_lt_of_ge hjr.le, ite_true, ite_false, zero_add] using hright j hj hjr
  have hC : (∑ j ∈ S, if j = i then (1 : ℝ) else 0) ≤ 1 := by
    by_cases hi : i ∈ S <;> simp [hi]
  rw [sum_filter] at hL hR
  linarith
theorem integer_row_bound (S : Finset ℕ) (i : ℕ) (c : ℝ) (hc : 0 < c) :
    (∑ j ∈ S, Real.exp (-c*((j : ℝ)-(i : ℝ))^2)) ≤ 1 + Real.sqrt (Real.pi/c) := by
  have hh := translated_sequence_bound S i
    (fun j ↦ Real.exp (-c*((j : ℝ)-(i : ℝ))^2))
    (fun n ↦ Real.exp (-c*((n+1 : ℕ) : ℝ)^2))
    (gaussian_tail_summable c hc) (fun _ ↦ (Real.exp_pos _).le) (by simp) (by
      intro j hj hji
      apply le_of_eq
      have he : i-j-1+1 = i-j := by omega
      rw [he, Nat.cast_sub hji.le]
      congr 1
      ring) (by
      intro j hj hij
      apply le_of_eq
      have he : j-i-1+1 = j-i := by omega
      rw [he, Nat.cast_sub hij.le])
  have ht := gaussian_tail_bound c hc
  linarith

theorem separated_row_bound (S : Finset ℕ) (w : ℕ → ℝ) (i : ℕ) (b δ : ℝ)
    (hb : 0 < b) (hδ : 0 < δ)
    (hgap : ∀ j ∈ S, δ * |(j : ℝ)-(i : ℝ)| ≤ |w j-w i|) :
    (∑ j ∈ S, Real.exp (-((w i-w j)^2/(4*b)))) ≤
      1 + Real.sqrt (Real.pi / (δ^2/(4*b))) := by
  let c := δ^2/(4*b)
  have hc : 0 < c := by dsimp only [c]; positivity
  calc
    _ ≤ ∑ j ∈ S, Real.exp (-c*((j : ℝ)-(i : ℝ))^2) := by
      apply sum_le_sum
      intro j hj
      apply Real.exp_le_exp.mpr
      have hh := hgap j hj
      have hsq : δ^2 * ((j : ℝ)-(i : ℝ))^2 ≤ (w i-w j)^2 := by
        have hpos : 0 ≤ δ * |(j : ℝ)-(i : ℝ)| := mul_nonneg hδ.le (abs_nonneg _)
        have hx := sq_abs (w j-w i)
        have hy := sq_abs ((j : ℝ)-(i : ℝ))
        nlinarith [abs_nonneg (w j-w i)]
      calc
        _ ≤ -(δ^2 * ((j : ℝ)-(i : ℝ))^2 / (4*b)) :=
          neg_le_neg (div_le_div_of_nonneg_right hsq (by positivity))
        _ = _ := by dsimp only [c]; ring
    _ ≤ _ := integer_row_bound S i c hc

theorem ordered_log_gap (x y M : ℝ) (hx : 0 < x) (hy : 0 < y) (hyM : y ≤ M) (hxy : x ≤ y) :
    (y-x)/M ≤ Real.log y - Real.log x := by
  have hh := Real.one_sub_inv_le_log_of_pos (div_pos hy hx)
  rw [Real.log_div hy.ne' hx.ne'] at hh
  have he : 1 - (y/x)⁻¹ = (y-x)/y := by field_simp
  rw [he] at hh
  exact (div_le_div_of_nonneg_left (sub_nonneg.mpr hxy) hy hyM).trans hh

theorem absolute_log_gap (x y M : ℝ) (hx : 0 < x) (hy : 0 < y) (hxM : x ≤ M) (hyM : y ≤ M) :
    |y-x|/M ≤ |Real.log y - Real.log x| := by
  rcases le_total x y with hxy | hyx
  · rw [abs_of_nonneg (sub_nonneg.mpr hxy), abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hx hxy))]
    exact ordered_log_gap x y M hx hy hyM hxy
  · rw [abs_sub_comm y x, abs_sub_comm (Real.log y) (Real.log x),
      abs_of_nonneg (sub_nonneg.mpr hyx), abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hy hyx))]
    exact ordered_log_gap y x M hy hx hxM hyx

theorem integer_log_gap (M i j : ℕ) (hi : 0 < i) (hj : 0 < j) (hiM : i ≤ M) (hjM : j ≤ M) :
    (1/(M : ℝ)) * |(j : ℝ)-(i : ℝ)| ≤ |Real.log j - Real.log i| := by
  have hh := absolute_log_gap (i : ℝ) (j : ℝ) (M : ℝ)
    (by exact_mod_cast hi) (by exact_mod_cast hj) (by exact_mod_cast hiM) (by exact_mod_cast hjM)
  calc
    _ = |(j : ℝ)-(i : ℝ)| / (M : ℝ) := by ring
    _ ≤ _ := hh

theorem logarithmic_row_bound (S : Finset ℕ) (M : ℕ) (hM : 0 < M)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ M) (i : ℕ) (hi : i ∈ S) (b : ℝ) (hb : 0 < b) :
    (∑ j ∈ S, Real.exp (-((Real.log i-Real.log j)^2/(4*b)))) ≤
      1 + Real.sqrt (Real.pi / ((1/(M : ℝ))^2/(4*b))) := by
  apply separated_row_bound S (fun n ↦ Real.log n) i b (1/(M : ℝ)) hb (by positivity)
  intro j hj
  exact integer_log_gap M i j (hS i hi).1 (hS j hj).1 (hS i hi).2 (hS j hj).2

end GaussianFrequencyRowBound
