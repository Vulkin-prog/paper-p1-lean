module

public import PaperP1.Analysis.PowerSeriesTail
public import Mathlib.NumberTheory.Harmonic.Bounds

/-! # The tail of a product of two positive integers

Every series is proved summable. The constants depend only on the fixed
exponent, and the cutoff is any real T≥1.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IntegerProductTail

open Finset PaperP1.PowerSeriesTail

def pairTerm (s T : ℝ) (p : ℕ × ℕ) : ℝ :=
  if T < (p.1 + 1 : ℝ) * (p.2 + 1 : ℝ) then weight s p.1 * weight s p.2 else 0

def row (s T : ℝ) (a : ℕ) : ℝ := weight s a * tail s (T / (a + 1 : ℝ))

def productTail (s T : ℝ) : ℝ := ∑' p : ℕ × ℕ, pairTerm s T p

def productConstant (s : ℝ) : ℝ :=
  constant s * ((1 + total s) / Real.log 2 + 1)

theorem pairTerm_nonneg (s T : ℝ) (p : ℕ × ℕ) : 0 ≤ pairTerm s T p := by
  unfold pairTerm
  split_ifs
  · exact mul_nonneg (weight_nonneg _ _) (weight_nonneg _ _)
  · exact le_rfl

theorem pairTerm_eq_power (s T : ℝ) (a b : ℕ) :
    pairTerm s T (a, b) =
      if T < (a + 1 : ℝ) * (b + 1 : ℝ) then
        ((a + 1 : ℝ) * (b + 1 : ℝ)) ^ (-s) else 0 := by
  unfold pairTerm weight
  rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ a + 1) (by positivity : (0 : ℝ) ≤ b + 1)]

theorem summable_pairTerm (s T : ℝ) (hs : 1 < s) : Summable (pairTerm s T) := by
  have hprod := (summable_weight s hs).mul_of_nonneg (summable_weight s hs)
    (weight_nonneg s) (weight_nonneg s)
  apply hprod.of_nonneg_of_le (pairTerm_nonneg s T)
  intro p
  unfold pairTerm
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (weight_nonneg _ _) (weight_nonneg _ _)

theorem pairTerm_factor (s T : ℝ) (a b : ℕ) :
    pairTerm s T (a, b) = weight s a * tailTerm s (T / (a + 1 : ℝ)) b := by
  have ha : (0 : ℝ) < a + 1 := by positivity
  have hcond : T / (a + 1 : ℝ) < (b + 1 : ℝ) ↔
      T < (a + 1 : ℝ) * (b + 1 : ℝ) := by
    rw [div_lt_iff₀ ha, mul_comm (b + 1 : ℝ) (a + 1 : ℝ)]
  unfold pairTerm tailTerm
  simp only [hcond]
  split_ifs <;> simp

theorem row_eq_tsum (s T : ℝ) (a : ℕ) : row s T a = ∑' b, pairTerm s T (a, b) := by
  simp only [pairTerm_factor, tsum_mul_left, row, tail]

theorem productTail_eq_rows (s T : ℝ) (hs : 1 < s) :
    productTail s T = ∑' a, row s T a := by
  rw [productTail, (summable_pairTerm s T hs).tsum_prod]
  apply tsum_congr
  intro a
  exact (row_eq_tsum s T a).symm

theorem row_nonneg (s T : ℝ) (a : ℕ) : 0 ≤ row s T a :=
  mul_nonneg (weight_nonneg _ _) (tail_nonneg _ _)

theorem row_le_total_weight (s T : ℝ) (hs : 1 < s) (a : ℕ) :
    row s T a ≤ total s * weight s a := by
  calc
    _ ≤ weight s a * total s :=
      mul_le_mul_of_nonneg_left (tail_le_total s _ hs) (weight_nonneg _ _)
    _ = _ := mul_comm _ _

theorem summable_row (s T : ℝ) (hs : 1 < s) : Summable (row s T) :=
  ((summable_weight s hs).mul_left (total s)).of_nonneg_of_le
    (row_nonneg s T) (row_le_total_weight s T hs)

theorem small_row_bound (s : ℝ) (hs : 1 < s) (T : ℝ) (a : ℕ)
    (haT : (a + 1 : ℝ) ≤ T) :
    row s T a ≤ constant s * T ^ (1 - s) * (a + 1 : ℝ)⁻¹ := by
  have ha : (0 : ℝ) < a + 1 := by positivity
  have hTa : 1 ≤ T / (a + 1 : ℝ) := (le_div_iff₀ ha).mpr (by simpa using haT)
  have hpower : (a + 1 : ℝ) ^ (-s) / (a + 1 : ℝ) ^ (1 - s) = (a + 1 : ℝ)⁻¹ := by
    rw [← Real.rpow_sub ha, show -s - (1 - s) = (-1 : ℝ) by ring, Real.rpow_neg_one]
  calc
    _ ≤ weight s a * (constant s * (T / (a + 1 : ℝ)) ^ (1 - s)) :=
      mul_le_mul_of_nonneg_left (tail_le_power s hs _ hTa) (weight_nonneg _ _)
    _ = constant s * T ^ (1 - s) *
        ((a + 1 : ℝ) ^ (-s) / (a + 1 : ℝ) ^ (1 - s)) := by
      rw [Real.div_rpow (ha.le.trans haT) ha.le]
      unfold weight
      ring
    _ = _ := by rw [hpower]

theorem small_rows_bound (s : ℝ) (hs : 1 < s) (T : ℝ) (hT : 1 ≤ T) :
    (∑ a ∈ range (Nat.floor T), row s T a) ≤
      constant s * T ^ (1 - s) * (1 + Real.log T) := by
  have hh : (∑ a ∈ range (Nat.floor T), (a + 1 : ℝ)⁻¹) ≤ 1 + Real.log T := by
    simpa only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
      Rat.cast_add, Rat.cast_one, Nat.cast_add, Nat.cast_one]
      using harmonic_floor_le_one_add_log T hT
  calc
    _ ≤ ∑ a ∈ range (Nat.floor T), constant s * T ^ (1 - s) * (a + 1 : ℝ)⁻¹ := by
      apply sum_le_sum
      intro a ha
      apply small_row_bound s hs T a
      have hnat : a + 1 ≤ Nat.floor T := mem_range.mp ha
      exact (by exact_mod_cast hnat : (a + 1 : ℝ) ≤ Nat.floor T).trans (Nat.floor_le (by linarith))
    _ = constant s * T ^ (1 - s) * ∑ a ∈ range (Nat.floor T), (a + 1 : ℝ)⁻¹ := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hh
      (mul_nonneg (constant_pos s hs).le (Real.rpow_nonneg (by linarith) _))

theorem large_rows_bound (s : ℝ) (hs : 1 < s) (T : ℝ) (hT : 1 ≤ T) :
    (∑' a : ℕ, row s T (a + Nat.floor T)) ≤ total s * (constant s * T ^ (1 - s)) := by
  have hr : Summable (fun a ↦ row s T (a + Nat.floor T)) :=
    (summable_nat_add_iff (Nat.floor T)).mpr (summable_row s T hs)
  have hw : Summable (fun a ↦ total s * weight s (a + Nat.floor T)) :=
    ((summable_nat_add_iff (Nat.floor T)).mpr (summable_weight s hs)).mul_left (total s)
  calc
    _ ≤ ∑' a : ℕ, total s * weight s (a + Nat.floor T) :=
      hr.tsum_le_tsum (fun a ↦ row_le_total_weight s T hs _) hw
    _ = total s * tail s T := by
      rw [tsum_mul_left, tail_eq_shifted s T hs (by linarith)]
      congr 1
      apply tsum_congr
      intro a
      simp only [weight, Nat.cast_add]
    _ ≤ _ := mul_le_mul_of_nonneg_left (tail_le_power s hs T hT) (total_nonneg s)

theorem productTail_harmonic_bound (s : ℝ) (hs : 1 < s) (T : ℝ) (hT : 1 ≤ T) :
    productTail s T ≤ constant s * T ^ (1 - s) * (1 + total s + Real.log T) := by
  rw [productTail_eq_rows s T hs, ← (summable_row s T hs).sum_add_tsum_nat_add (Nat.floor T)]
  have h := add_le_add (small_rows_bound s hs T hT) (large_rows_bound s hs T hT)
  convert h using 1
  ring

theorem productConstant_pos (s : ℝ) (hs : 1 < s) : 0 < productConstant s := by
  unfold productConstant
  have hz := total_nonneg s
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  exact mul_pos (constant_pos s hs) (by positivity)

theorem logarithmic_budget (s : ℝ) (hs : 1 < s) (T : ℝ) (hT : 1 ≤ T) :
    constant s * (1 + total s + Real.log T) ≤ productConstant s * Real.log (2 * T) := by
  have hc := (constant_pos s hs).le
  have hz := total_nonneg s
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hdiv : 0 ≤ (1 + total s) / Real.log 2 := div_nonneg (by linarith) hlog2.le
  have hcoeff : constant s ≤ productConstant s := by
    unfold productConstant
    nlinarith [mul_nonneg hc hdiv]
  have heq : productConstant s * Real.log 2 =
      constant s * (1 + total s) + constant s * Real.log 2 := by
    unfold productConstant
    field_simp
  have hconst : constant s * (1 + total s) ≤ productConstant s * Real.log 2 := by
    rw [heq]
    nlinarith [mul_nonneg hc hlog2.le]
  have hscale := mul_le_mul_of_nonneg_right hcoeff hlogT
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by linarith : T ≠ 0)]
  nlinarith

theorem productTail_bound (s : ℝ) (hs : 1 < s) (T : ℝ) (hT : 1 ≤ T) :
    productTail s T ≤ productConstant s * T ^ (1 - s) * Real.log (2 * T) := by
  calc
    _ ≤ constant s * T ^ (1 - s) * (1 + total s + Real.log T) :=
      productTail_harmonic_bound s hs T hT
    _ = T ^ (1 - s) * (constant s * (1 + total s + Real.log T)) := by ring
    _ ≤ T ^ (1 - s) * (productConstant s * Real.log (2 * T)) :=
      mul_le_mul_of_nonneg_left (logarithmic_budget s hs T hT)
        (Real.rpow_nonneg (by linarith) _)
    _ = _ := by ring

/-- One positive constant, chosen before every real threshold T≥1. -/
theorem companion_T20_2 (s : ℝ) (hs : 1 < s) :
    ∃ K : ℝ, 0 < K ∧ ∀ T : ℝ, 1 ≤ T →
      productTail s T ≤ K * T ^ (1 - s) * Real.log (2 * T) :=
  ⟨productConstant s, productConstant_pos s hs, fun T hT ↦ productTail_bound s hs T hT⟩

end PaperP1.IntegerProductTail
