module

public import PaperP1.Analysis.RungePowerSeries
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.SpecificLimits.Normed

/-! # Real evaluation of absolutely convergent rational formal series -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RealSeriesEvaluation

open Finset

def term (f : PowerSeries ℚ) (t : ℝ) (n : ℕ) : ℝ := ((PowerSeries.coeff n f : ℚ) : ℝ) * t ^ n

def value (f : PowerSeries ℚ) (t : ℝ) : ℝ := ∑' n, term f t n

def AbsolutelySummable (f : PowerSeries ℚ) (t : ℝ) : Prop := Summable (fun n ↦ ‖term f t n‖)

theorem term_add (f g : PowerSeries ℚ) (t : ℝ) (n : ℕ) : term (f + g) t n = term f t n + term g t n := by
  simp only [term, map_add, Rat.cast_add, add_mul]

theorem term_mul (f g : PowerSeries ℚ) (t : ℝ) (n : ℕ) :
    term (f * g) t n = ∑ p ∈ Finset.antidiagonal n, term f t p.1 * term g t p.2 := by
  rw [term, PowerSeries.coeff_mul]
  push_cast
  rw [sum_mul]
  apply sum_congr rfl
  intro p hp
  have hn := Finset.mem_antidiagonal.mp hp
  rw [← hn, pow_add]
  dsimp [term]
  ring

theorem absolutelySummable_C (c : ℚ) (t : ℝ) : AbsolutelySummable (PowerSeries.C c) t := by
  apply summable_of_ne_finset_zero (s := {0})
  intro n hn
  have hn₀ : n ≠ 0 := by simpa only [mem_singleton] using hn
  simp [term, PowerSeries.coeff_C, hn₀]

theorem value_C (c : ℚ) (t : ℝ) : value (PowerSeries.C c) t = (c : ℝ) := by
  have he : term (PowerSeries.C c) t = fun n ↦ if n = 0 then (c : ℝ) else 0 := by
    funext n
    by_cases hn : n = 0 <;> simp [term, PowerSeries.coeff_C, hn]
  rw [value, he, tsum_ite_eq]

theorem absolutelySummable_X (t : ℝ) : AbsolutelySummable (PowerSeries.X : PowerSeries ℚ) t := by
  apply summable_of_ne_finset_zero (s := {1})
  intro n hn
  have hn₁ : n ≠ 1 := by simpa only [mem_singleton] using hn
  simp [term, PowerSeries.coeff_X, hn₁]

theorem value_X (t : ℝ) : value (PowerSeries.X : PowerSeries ℚ) t = t := by
  have he : term (PowerSeries.X : PowerSeries ℚ) t = fun n ↦ if n = 1 then t else 0 := by
    funext n
    by_cases hn : n = 1 <;> simp [term, PowerSeries.coeff_X, hn]
  rw [value, he, tsum_ite_eq]

theorem absolutelySummable_add (f g : PowerSeries ℚ) (t : ℝ)
    (hf : AbsolutelySummable f t) (hg : AbsolutelySummable g t) : AbsolutelySummable (f + g) t := by
  exact (hf.add hg).of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ by rw [term_add]; exact norm_add_le _ _)

theorem value_add (f g : PowerSeries ℚ) (t : ℝ)
    (hf : AbsolutelySummable f t) (hg : AbsolutelySummable g t) : value (f + g) t = value f t + value g t := by
  unfold value
  simp only [term_add]
  exact hf.of_norm.tsum_add hg.of_norm

theorem absolutelySummable_mul (f g : PowerSeries ℚ) (t : ℝ)
    (hf : AbsolutelySummable f t) (hg : AbsolutelySummable g t) : AbsolutelySummable (f * g) t := by
  unfold AbsolutelySummable
  have hp := summable_norm_sum_mul_antidiagonal_of_summable_norm hf hg
  simpa only [← term_mul] using hp

theorem value_mul (f g : PowerSeries ℚ) (t : ℝ)
    (hf : AbsolutelySummable f t) (hg : AbsolutelySummable g t) : value (f * g) t = value f t * value g t := by
  unfold value
  simp only [term_mul]
  exact (tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg).symm

theorem absolutelySummable_prod {ι : Type*} (S : Finset ι) (f : ι → PowerSeries ℚ) (t : ℝ)
    (hf : ∀ i ∈ S, AbsolutelySummable (f i) t) : AbsolutelySummable (∏ i ∈ S, f i) t := by
  classical
  revert hf
  induction S using Finset.induction_on with
  | empty =>
    intro _
    simpa only [prod_empty, map_one] using absolutelySummable_C 1 t
  | @insert i S hi ih =>
    intro h
    rw [prod_insert hi]
    exact absolutelySummable_mul _ _ t (h i (mem_insert_self i S)) (ih (fun j hj ↦ h j (mem_insert_of_mem hj)))

theorem value_prod {ι : Type*} (S : Finset ι) (f : ι → PowerSeries ℚ) (t : ℝ)
    (hf : ∀ i ∈ S, AbsolutelySummable (f i) t) : value (∏ i ∈ S, f i) t = ∏ i ∈ S, value (f i) t := by
  classical
  revert hf
  induction S using Finset.induction_on with
  | empty =>
    intro _
    simpa only [prod_empty, map_one, Rat.cast_one] using value_C 1 t
  | @insert i S hi ih =>
    intro h
    have hS := fun j hj ↦ h j (mem_insert_of_mem hj)
    rw [prod_insert hi, prod_insert hi, value_mul _ _ t (h i (mem_insert_self i S)) (absolutelySummable_prod S f t hS), ih hS]

theorem geometric_summability (f : PowerSeries ℚ) (t C R : ℝ) (hR : 0 ≤ R)
    (hsmall : R * |t| < 1) (hcoeff : ∀ n, |((PowerSeries.coeff n f : ℚ) : ℝ)| ≤ C * R ^ n) :
    AbsolutelySummable f t := by
  have hgeo := (summable_geometric_of_lt_one (mul_nonneg hR (abs_nonneg t)) hsmall).mul_left C
  apply hgeo.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
  intro n
  simp only [term, norm_mul, Real.norm_eq_abs, abs_pow]
  calc
    _ ≤ (C * R ^ n) * |t| ^ n := mul_le_mul_of_nonneg_right (hcoeff n) (pow_nonneg (abs_nonneg t) n)
    _ = _ := by rw [mul_pow]; ring

end PaperP1.RealSeriesEvaluation
